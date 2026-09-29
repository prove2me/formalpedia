-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_recAt_of_ge
-- name    : BookProof.SirkBandLedger.recAt_of_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:07:54.902753+00:00
-- url     : https://prove2.me/theorems/21d4877c-27c1-4cc2-8d9d-6a0788ab110d
-- title:
--   {L : List BandRecord} {m : ℕ} (hm : L.length - 1 ≤ m) : recAt L m = recAt L (L.length - 1)
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.recAt_of_ge` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.recAt_of_ge
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure

theorem BookProof.SirkBandLedger.recAt_of_ge {L : List BandRecord} {m : ℕ} (hm : L.length - 1 ≤ m) :
    recAt L m = recAt L (L.length - 1) := by sorry
