-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_ledger_width_eventually_const
-- name    : BookProof.SirkBandLedger.ledger_width_eventually_const
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:52:20.688104+00:00
-- url     : https://prove2.me/theorems/c61df90f-1dd1-475f-9c93-b4455915345a
-- title:
--   (L : List BandRecord) {m : ℕ} (hm : L.length - 1 ≤ m) : ledgerHi L m - ledgerLo L m = ledgerHi L (L.length - 1) - ledgerLo L (L.length - 1)
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.ledger_width_eventually_const` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.ledger_width_eventually_const
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure

theorem BookProof.SirkBandLedger.ledger_width_eventually_const (L : List BandRecord) {m : ℕ}
    (hm : L.length - 1 ≤ m) :
    ledgerHi L m - ledgerLo L m
      = ledgerHi L (L.length - 1) - ledgerLo L (L.length - 1) := by sorry
