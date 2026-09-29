-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_ledgerWf_step
-- name    : BookProof.SirkBandLedger.ledgerWf_step
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:51:31.783887+00:00
-- url     : https://prove2.me/theorems/246a146c-79c5-413f-b596-66ee8e62923f
-- title:
--   {L : List BandRecord} (h : LedgerWf L) {i : ℕ} (hi : i + 1 < L.length) : (L.getD i default).lo.toQ ≤ (L.getD (i + 1) default).lo.toQ ∧ (L.getD (i + 1) default).hi.toQ ≤ (L.getD i default).hi.toQ
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.ledgerWf_step` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.ledgerWf_step
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure

theorem BookProof.SirkBandLedger.ledgerWf_step {L : List BandRecord} (h : LedgerWf L) {i : ℕ}
    (hi : i + 1 < L.length) :
    (L.getD i default).lo.toQ ≤ (L.getD (i + 1) default).lo.toQ ∧
      (L.getD (i + 1) default).hi.toQ ≤ (L.getD i default).hi.toQ := by sorry
