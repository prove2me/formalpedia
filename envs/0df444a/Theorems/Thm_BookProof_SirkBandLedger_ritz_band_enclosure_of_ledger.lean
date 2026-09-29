-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_ritz_band_enclosure_of_ledger
-- name    : BookProof.SirkBandLedger.ritz_band_enclosure_of_ledger
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:13:24.985151+00:00
-- url     : https://prove2.me/theorems/e4f84150-7942-4fb3-9d32-98a67b329401
-- title:
--   [Nontrivial F] (A : F →L[ℂ] F) (hsa : IsSelfAdjoint A) (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re) (b : HilbertBasis ℕ ℂ F) {L : List BandRecord} (hwf : LedgerWf L) (hritz :...
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.ritz_band_enclosure_of_ledger` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.ritz_band_enclosure_of_ledger
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure



































open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.SirkBandLedger.ritz_band_enclosure_of_ledger [Nontrivial F] (A : F →L[ℂ] F)
    (hsa : IsSelfAdjoint A) (hpos : ∀ u : F, 0 ≤ (inner ℂ u (A u) : ℂ).re)
    (b : HilbertBasis ℕ ℂ F) {L : List BandRecord} (hwf : LedgerWf L)
    (hritz : ∀ m, ritzInf (finiteModeRestrict A b) (galerkinSpan b (m + 1)) ∈
      Set.Icc (ledgerLo L m) (ledgerHi L m)) :
    IsPositiveSelfAdjointExtension (finiteModeRestrict A b) (topRestrict A) ∧
      ∀ m, sInf (spectrum ℝ A) ∈ Set.Icc (ledgerLo L m) (ledgerHi L m) := by sorry
