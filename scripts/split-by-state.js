/**
 * Split the read-only US city database into one cities.json per state.
 *
 * Reads:  all-us-states-databases/state-city-databases/*_master_city_database.json
 * Writes: states-split/<state-name>/cities.json
 *
 * Does not modify, rename, or delete any source file.
 *
 * Re-run from the project root or from anywhere:
 *   node scripts/split-by-state.js
 *
 * The 13-city skip list is the Census places flagged in the completeness check.
 * Matching is limited to that state, so the same name in another state is kept.
 */

"use strict";

const fs = require("fs");
const https = require("https");
const path = require("path");

const ROOT = path.resolve(__dirname, "..");
const SRC_DIR = path.join(ROOT, "all-us-states-databases", "state-city-databases");
const OUT_DIR = path.join(ROOT, "states-split");
const ZIP_FILE = path.join(__dirname, "data", "tab20_zcta520_place20_natl.txt");
const POINT_CACHE = path.join(__dirname, "data", "zcta-point-cache.json");
const ZIP_URL =
  "https://www2.census.gov/geo/docs/maps-data/data/rel2020/zcta520/tab20_zcta520_place20_natl.txt";

const STATE_SLUGS = {
  AL: "alabama",
  AK: "alaska",
  AZ: "arizona",
  AR: "arkansas",
  CA: "california",
  CO: "colorado",
  CT: "connecticut",
  DE: "delaware",
  FL: "florida",
  GA: "georgia",
  HI: "hawaii",
  ID: "idaho",
  IL: "illinois",
  IN: "indiana",
  IA: "iowa",
  KS: "kansas",
  KY: "kentucky",
  LA: "louisiana",
  ME: "maine",
  MD: "maryland",
  MA: "massachusetts",
  MI: "michigan",
  MN: "minnesota",
  MS: "mississippi",
  MO: "missouri",
  MT: "montana",
  NE: "nebraska",
  NV: "nevada",
  NH: "new-hampshire",
  NJ: "new-jersey",
  NM: "new-mexico",
  NY: "new-york",
  NC: "north-carolina",
  ND: "north-dakota",
  OH: "ohio",
  OK: "oklahoma",
  OR: "oregon",
  PA: "pennsylvania",
  RI: "rhode-island",
  SC: "south-carolina",
  SD: "south-dakota",
  TN: "tennessee",
  TX: "texas",
  UT: "utah",
  VT: "vermont",
  VA: "virginia",
  WA: "washington",
  WV: "west-virginia",
  WI: "wisconsin",
  WY: "wyoming",
};

/** Census places called out as already handled. State-scoped. */
const SKIP_CITIES = [
  { state: "AL", name: "Cherokee Ridge" },
  { state: "FL", name: "Biscayne Gardens" },
  { state: "FL", name: "Southport" },
  { state: "MA", name: "Amesbury" },
  { state: "MA", name: "Easthampton" },
  { state: "MA", name: "Methuen" },
  { state: "MA", name: "Watertown" },
  { state: "MN", name: "Empire" },
  { state: "MN", name: "Minnetonka Beach" },
  { state: "NM", name: "Sullivan" },
  { state: "NY", name: "Morristown" },
  { state: "VT", name: "Jericho Center" },
  { state: "WI", name: "Lisbon" },
];

const SKIP_KEYS = new Set(
  SKIP_CITIES.map((item) => `${item.state}|${item.name.toLowerCase()}`)
);

const LEGAL_SUFFIX =
  /\s+(census designated place|cdp|city|town|village|borough|municipality|township|comunidad|zona urbana|corporation|unified government|consolidated government|metropolitan government|metro government|urban county)$/i;

function cleanCityName(raw) {
  let name = String(raw || "").trim().replace(/\s+/g, " ");
  name = name.replace(/\s*\(balance\)\s*$/i, "").trim();
  name = name.replace(LEGAL_SUFFIX, "").trim();
  return name;
}

/** Extra suffix pass so "Amesbury Town city" matches the skip name "Amesbury". */
function skipName(raw) {
  return cleanCityName(raw).replace(LEGAL_SUFFIX, "").trim().toLowerCase();
}

function cleanCounty(value) {
  if (typeof value !== "string") return "";
  return value.trim().replace(/\s+/g, " ").replace(/\s+county$/i, "").trim();
}

function readCounty(city) {
  const radon = city.hazards && city.hazards.radon_zone && city.hazards.radon_zone.county_name;
  const schools = city.local_entities && city.local_entities.schools && city.local_entities.schools.county_name;
  return cleanCounty(radon) || cleanCounty(schools);
}

/**
 * April 1, 2020 Census counts for places whose ACS population is null.
 * ACS estimates are suppressed for the three New York CDPs, and Louisville
 * city has no ACS total separate from the metro-government balance record.
 */
const CENSUS_2020_POPULATION = {
  "2148000": 246161,
  "3608026": 62387,
  "3678487": 1709,
  "3683294": 12990,
};

function readPopulation(city) {
  const raw = city.demographics && city.demographics.population;
  if (raw !== null && raw !== undefined && raw !== "") {
    const n = typeof raw === "number" ? raw : Number(raw);
    if (Number.isFinite(n) && n >= 0) {
      const rounded = Math.round(n);
      return Math.abs(n - rounded) < 1e-6 ? rounded : n;
    }
  }
  const fips = String(city.place_fips || "").padStart(7, "0");
  return Object.prototype.hasOwnProperty.call(CENSUS_2020_POPULATION, fips)
    ? CENSUS_2020_POPULATION[fips]
    : null;
}

function readPayout(city) {
  const candidates = [city.payout, city.demographics && city.demographics.payout];
  for (const value of candidates) {
    if (typeof value === "number" && Number.isFinite(value)) return value;
  }
  return null;
}

function readZipCodes(city, zipIndex) {
  const candidates = [city.zip_codes, city.zips, city.zipCodes];
  for (const value of candidates) {
    if (!Array.isArray(value)) continue;
    const zips = value
      .map((zip) => (zip === null || zip === undefined ? "" : String(zip).trim()))
      .filter((zip) => /^\d{5}$/.test(zip));
    if (zips.length) return [...new Set(zips)].sort();
  }

  const fips = String(city.place_fips || "").padStart(7, "0");
  const match = zipIndex.get(fips);
  if (!match || !match.length) return null;
  return match;
}

/**
 * Census 2020 ZCTA-to-place overlaps.
 * Keep a ZIP when it covers at least 1% of the place, or at least 5% of that
 * ZIP is inside the place. That drops boundary slivers and keeps small ZIPs
 * that sit inside a large city. If nothing passes, use the single largest overlap.
 */
function loadZipIndex(filePath) {
  const text = fs.readFileSync(filePath, "utf8").replace(/^\uFEFF/, "");
  const lines = text.split(/\r?\n/);
  const header = lines[0].split("|");
  const col = Object.fromEntries(header.map((name, index) => [name, index]));
  const qualified = new Map();
  const best = new Map();

  for (let i = 1; i < lines.length; i += 1) {
    if (!lines[i]) continue;
    const parts = lines[i].split("|");
    const zip = parts[col.GEOID_ZCTA5_20];
    const geoid = parts[col.GEOID_PLACE_20];
    if (!zip || !geoid || !/^\d{5}$/.test(zip)) continue;

    const overlap = Number(parts[col.AREALAND_PART]) || 0;
    const placeLand = Number(parts[col.AREALAND_PLACE_20]) || 0;
    const zipLand = Number(parts[col.AREALAND_ZCTA5_20]) || 0;
    if (overlap <= 0) continue;

    const previous = best.get(geoid);
    if (!previous || overlap > previous.overlap) best.set(geoid, { zip, overlap });

    const placeShare = placeLand > 0 ? overlap / placeLand : 0;
    const zipShare = zipLand > 0 ? overlap / zipLand : 0;
    if (placeShare < 0.01 && zipShare < 0.05) continue;

    let zips = qualified.get(geoid);
    if (!zips) qualified.set(geoid, (zips = new Set()));
    zips.add(zip);
  }

  const index = new Map();
  for (const [geoid, row] of best) {
    const chosen = qualified.get(geoid);
    const zips = chosen ? [...chosen] : [row.zip];
    zips.sort();
    index.set(geoid, zips);
  }
  return index;
}

function ensureZipFile() {
  if (fs.existsSync(ZIP_FILE)) return;
  fs.mkdirSync(path.dirname(ZIP_FILE), { recursive: true });
  const { spawnSync } = require("child_process");
  const result = spawnSync(
    "powershell",
    [
      "-NoProfile",
      "-Command",
      `Invoke-WebRequest -Uri '${ZIP_URL}' -OutFile '${ZIP_FILE}' -UseBasicParsing`,
    ],
    { stdio: "inherit" }
  );
  if (result.status !== 0 || !fs.existsSync(ZIP_FILE)) {
    console.error(`Could not download Census ZIP relationship file: ${ZIP_URL}`);
    process.exit(1);
  }
}

function buildEntry(city, zipIndex) {
  const name = cleanCityName(city.city);
  const population = readPopulation(city);
  if (!name || population === null) return null;

  const county = readCounty(city);
  const zipCodes = readZipCodes(city, zipIndex);
  const payout = readPayout(city);
  const entry = { city: name };
  if (county) entry.county = county;
  if (zipCodes) entry.zip_codes = zipCodes;
  entry.population = population;
  if (payout !== null) entry.payout = payout;

  const lat = city.location && Number(city.location.lat);
  const lng = city.location && Number(city.location.lng);
  if (Number.isFinite(lat) && Number.isFinite(lng)) {
    entry._lat = lat;
    entry._lng = lng;
  }
  if (city.place_fips) entry._fips = String(city.place_fips).padStart(7, "0");
  const sourcePopulation = city.demographics && city.demographics.population;
  if (
    (sourcePopulation === null || sourcePopulation === undefined || sourcePopulation === "") &&
    entry._fips &&
    Object.prototype.hasOwnProperty.call(CENSUS_2020_POPULATION, entry._fips)
  ) {
    entry._populationFilled = true;
  }

  return entry;
}

function lookupZcta(lat, lng) {
  const url =
    "https://tigerweb.geo.census.gov/arcgis/rest/services/TIGERweb/tigerWMS_Current/MapServer/2/query" +
    `?geometry=${lng},${lat}&geometryType=esriGeometryPoint&inSR=4326` +
    "&spatialRel=esriSpatialRelIntersects&outFields=ZCTA5&returnGeometry=false&f=json";

  return new Promise((resolve, reject) => {
    const req = https.get(url, { headers: { "User-Agent": "states-split/1.0" } }, (res) => {
      let body = "";
      res.on("data", (chunk) => {
        body += chunk;
      });
      res.on("end", () => {
        if (res.statusCode !== 200) {
          reject(new Error(`TIGERweb HTTP ${res.statusCode}`));
          return;
        }
        try {
          const json = JSON.parse(body);
          const zip =
            json.features &&
            json.features[0] &&
            json.features[0].attributes &&
            json.features[0].attributes.ZCTA5;
          resolve(zip && /^\d{5}$/.test(String(zip)) ? String(zip) : null);
        } catch (err) {
          reject(err);
        }
      });
    });
    req.setTimeout(20000, () => req.destroy(new Error("TIGERweb timeout")));
    req.on("error", reject);
  });
}

async function lookupWithRetry(lat, lng) {
  let lastError;
  for (let attempt = 0; attempt < 3; attempt += 1) {
    try {
      return await lookupZcta(lat, lng);
    } catch (err) {
      lastError = err;
      await new Promise((resolve) => setTimeout(resolve, 500 * (attempt + 1)));
    }
  }
  throw lastError;
}

async function mapPool(items, limit, worker) {
  let next = 0;
  async function run() {
    while (next < items.length) {
      const index = next;
      next += 1;
      await worker(items[index], index);
    }
  }
  const workers = Math.min(limit, items.length);
  await Promise.all(Array.from({ length: workers }, () => run()));
}

async function fillPointZips(groups) {
  const cache = fs.existsSync(POINT_CACHE) ? JSON.parse(fs.readFileSync(POINT_CACHE, "utf8")) : {};
  const needed = new Map();

  for (const group of groups) {
    for (const row of group.rows) {
      if (row.zip_codes && row.zip_codes.length) continue;
      if (!row._fips || !Number.isFinite(row._lat) || !Number.isFinite(row._lng)) continue;
      if (Object.prototype.hasOwnProperty.call(cache, row._fips)) {
        if (cache[row._fips]) row.zip_codes = [cache[row._fips]];
        continue;
      }
      needed.set(row._fips, { lat: row._lat, lng: row._lng });
    }
  }

  const jobs = [...needed.entries()];
  if (jobs.length) {
    console.log(`Looking up ZIP codes for ${jobs.length} places outside the 2020 crosswalk...`);
    let done = 0;
    await mapPool(jobs, 8, async ([fips, coords]) => {
      try {
        cache[fips] = await lookupWithRetry(coords.lat, coords.lng);
      } catch (err) {
        cache[fips] = null;
        console.error(`  ZIP lookup failed for ${fips}: ${err.message}`);
      }
      done += 1;
      if (done % 100 === 0 || done === jobs.length) console.log(`  ${done}/${jobs.length}`);
    });
    fs.mkdirSync(path.dirname(POINT_CACHE), { recursive: true });
    fs.writeFileSync(POINT_CACHE, `${JSON.stringify(cache)}\n`);
  }

  for (const group of groups) {
    for (const row of group.rows) {
      if ((!row.zip_codes || !row.zip_codes.length) && row._fips && cache[row._fips]) {
        row.zip_codes = [cache[row._fips]];
      }
      delete row._lat;
      delete row._lng;
      delete row._fips;
    }
  }
}

function entryScore(entry) {
  return entry.population;
}

function processState(abbr, cities, zipIndex) {
  const skipped = [];
  const kept = new Map();
  const foundSkip = new Set();

  for (const city of cities) {
    const rawName = typeof city.city === "string" ? city.city.trim() : "";
    const matchedSkip = skipName(rawName);
    if (SKIP_KEYS.has(`${abbr}|${matchedSkip}`)) {
      foundSkip.add(matchedSkip);
      skipped.push({
        city: rawName,
        reason: "on the 13-city skip list",
      });
      continue;
    }

    const population = readPopulation(city);
    if (!rawName) {
      skipped.push({ city: "(blank)", reason: "missing city name" });
      continue;
    }
    if (population === null) {
      skipped.push({ city: rawName, reason: "missing population" });
      continue;
    }

    const entry = buildEntry(city, zipIndex);
    if (!entry) {
      skipped.push({ city: rawName, reason: "missing city name or population" });
      continue;
    }

    const countyKey = (entry.county || "").toLowerCase();
    const key = `${entry.city.toLowerCase()}|${countyKey}`;
    const existing = kept.get(key);
    if (!existing) {
      kept.set(key, entry);
      continue;
    }

    if (entryScore(entry) > entryScore(existing)) {
      skipped.push({
        city: existing.city,
        county: existing.county || "",
        reason: `duplicate of ${entry.city}${entry.county ? ` (${entry.county})` : ""}; kept the record with population ${entry.population}`,
      });
      kept.set(key, entry);
    } else {
      skipped.push({
        city: entry.city,
        county: entry.county || "",
        reason: `duplicate of ${existing.city}${existing.county ? ` (${existing.county})` : ""}; kept the record with population ${existing.population}`,
      });
    }
  }

  const rows = [...kept.values()].sort((a, b) => {
    const byCity = a.city.localeCompare(b.city, "en", { sensitivity: "base" });
    if (byCity !== 0) return byCity;
    return (a.county || "").localeCompare(b.county || "", "en", { sensitivity: "base" });
  });

  return { rows, skipped, foundSkip };
}

/** Source files contain bare NaN tokens. Convert them in memory only. */
function parseSource(text) {
  const normalized = text
    .replace(/:\s*NaN\b/g, ": null")
    .replace(/:\s*-Infinity\b/g, ": null")
    .replace(/:\s*Infinity\b/g, ": null");
  return JSON.parse(normalized);
}

function orderedEntry(row) {
  const entry = { city: row.city };
  if (row.county) entry.county = row.county;
  if (row.zip_codes && row.zip_codes.length) entry.zip_codes = row.zip_codes;
  entry.population = row.population;
  if (typeof row.payout === "number" && Number.isFinite(row.payout)) entry.payout = row.payout;
  return entry;
}

async function main() {
  if (!fs.existsSync(SRC_DIR)) {
    console.error(`Source database not found: ${SRC_DIR}`);
    process.exit(1);
  }

  fs.mkdirSync(OUT_DIR, { recursive: true });
  ensureZipFile();
  const zipIndex = loadZipIndex(ZIP_FILE);

  const files = fs
    .readdirSync(SRC_DIR)
    .filter((name) => name.endsWith("_master_city_database.json"))
    .sort();

  const perState = [];
  const allSkipped = [];
  const excluded = [];
  const groups = [];
  const skipHits = new Map(SKIP_CITIES.map((item) => [`${item.state}|${item.name.toLowerCase()}`, false]));

  for (const fileName of files) {
    const fullPath = path.join(SRC_DIR, fileName);
    const data = parseSource(fs.readFileSync(fullPath, "utf8"));
    const abbr = (data._meta && data._meta.state) || fileName.slice(0, 2).toUpperCase();
    const cities = Array.isArray(data.cities) ? data.cities : [];
    const slug = STATE_SLUGS[abbr];

    if (!slug) {
      excluded.push({ state: abbr, cities: cities.length, reason: "not one of the 50 states" });
      continue;
    }

    const { rows, skipped, foundSkip } = processState(abbr, cities, zipIndex);
    for (const name of foundSkip) {
      skipHits.set(`${abbr}|${name}`, true);
    }

    groups.push({ abbr, slug, rows });
    for (const item of skipped) {
      allSkipped.push({ state: abbr, ...item });
    }
  }

  await fillPointZips(groups);

  for (const group of groups) {
    const outDir = path.join(OUT_DIR, group.slug);
    fs.mkdirSync(outDir, { recursive: true });
    fs.writeFileSync(
      path.join(outDir, "cities.json"),
      `${JSON.stringify(group.rows.map(orderedEntry), null, 2)}\n`,
      "utf8"
    );
    perState.push({
      state: group.abbr,
      slug: group.slug,
      count: group.rows.length,
      withZips: group.rows.filter((row) => row.zip_codes && row.zip_codes.length).length,
    });
  }

  perState.sort((a, b) => a.slug.localeCompare(b.slug));

  console.log(`States created: ${perState.length}`);
  console.log("");
  console.log("Cities per state (with ZIP codes):");
  for (const row of perState) {
    const missing = row.count - row.withZips;
    const note = missing ? ` — ${missing} without ZIP codes` : "";
    console.log(`  ${row.slug}: ${row.count} (${row.withZips} with ZIP codes)${note}`);
  }

  console.log("");
  console.log("Excluded source files:");
  for (const row of excluded) {
    console.log(`  ${row.state}: ${row.cities} cities — ${row.reason}`);
  }

  console.log("");
  console.log("13-city skip list:");
  for (const item of SKIP_CITIES) {
    const hit = skipHits.get(`${item.state}|${item.name.toLowerCase()}`);
    const why = hit
      ? "found in source and left out"
      : "not in the source database, so there was no record to write";
    console.log(`  ${item.state} ${item.name}: ${why}`);
  }

  const otherSkipped = allSkipped.filter((item) => item.reason !== "on the 13-city skip list");
  console.log("");
  console.log(`Other skipped records: ${otherSkipped.length}`);
  for (const item of otherSkipped) {
    const county = item.county ? `, ${item.county}` : "";
    console.log(`  ${item.state} ${item.city}${county}: ${item.reason}`);
  }

  const filled = [];
  for (const group of groups) {
    for (const row of group.rows) {
      if (row._populationFilled) filled.push(`${group.abbr} ${row.city}: ${row.population}`);
    }
  }
  console.log("");
  console.log(`Population filled from the 2020 Census: ${filled.length}`);
  for (const line of filled) console.log(`  ${line}`);

  const written = perState.reduce((sum, row) => sum + row.count, 0);
  console.log("");
  console.log(`Total cities written: ${written}`);
  console.log(`Output: ${OUT_DIR}`);
}

main().catch((err) => {
  console.error(err);
  process.exit(1);
});
