-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_ledger_width_tendsto_zero_iff
-- name    : BookProof.SirkBandLedger.ledger_width_tendsto_zero_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T14:33:40.167507+00:00
-- url     : https://prove2.me/theorems/3d8f8c7e-27e3-460d-a261-4d2bc294190f
-- title:
--   (L : List BandRecord) : Filter.Tendsto (fun m => ledgerHi L m - ledgerLo L m) Filter.atTop (nhds 0) ↔ ledgerHi L (L.length - 1) - ledgerLo L (L.length - 1) = 0
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.ledger_width_tendsto_zero_iff` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.ledger_width_tendsto_zero_iff
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure

theorem BookProof.SirkBandLedger.ledger_width_tendsto_zero_iff (L : List BandRecord) :
    Filter.Tendsto (fun m => ledgerHi L m - ledgerLo L m) Filter.atTop (nhds 0) ↔
      ledgerHi L (L.length - 1) - ledgerLo L (L.length - 1) = 0 := by sorry
