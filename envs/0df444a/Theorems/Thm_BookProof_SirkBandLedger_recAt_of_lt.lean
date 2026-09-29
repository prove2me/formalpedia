-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_recAt_of_lt
-- name    : BookProof.SirkBandLedger.recAt_of_lt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:09:13.736302+00:00
-- url     : https://prove2.me/theorems/22cda6fb-71ac-41f6-b8f1-6219170dc7d9
-- title:
--   {L : List BandRecord} {m : ℕ} (hm : m < L.length) : recAt L m = L.getD m default
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.recAt_of_lt` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.recAt_of_lt
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure

theorem BookProof.SirkBandLedger.recAt_of_lt {L : List BandRecord} {m : ℕ} (hm : m < L.length) :
    recAt L m = L.getD m default := by sorry
