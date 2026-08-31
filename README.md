# Racine-leads

Motivated-seller lead scraper for **Racine County, WI** — cloned from the Bexar/Milwaukee system.

Pipeline: county sources → scrape → normalize → hash/dedupe → NEW/CHANGED detection → score → export.

**Sources**
- WCCA circuit-court records (countyNo 51): mortgage foreclosures (CV/30404), money judgments (CV/30301), transcripts of judgment (TJ), state tax warrants (TW), probate (PR, 60-day lookback)
- Racine County Sheriff foreclosure-sale GIS points (upcoming auctions)
- Enrichment: Racine County Mapbook parcel layer (OWNERNME1/2, SITEADDRESS, PSTL mailing fields)

**Outputs**
- `dashboard/` — live dashboard (GitHub Pages) + `records.json`
- `data/ghl_export.csv` — GHL import
- `data/skiptrace_export.csv` — skip-trace list

Runs daily via GitHub Actions (13:00 UTC) and on manual dispatch.
