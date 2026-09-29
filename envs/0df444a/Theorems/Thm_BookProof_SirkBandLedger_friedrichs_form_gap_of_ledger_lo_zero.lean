-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_friedrichs_form_gap_of_ledger_lo_zero
-- name    : BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger_lo_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:18:46.320086+00:00
-- url     : https://prove2.me/theorems/e9135608-7889-485f-ab42-d42b3d9b4a6b
-- title:
--   (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn (finiteModeDomain b) H) (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x) {L : List BandRecord} (hwf...
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger_lo_zero` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger_lo_zero
import Mathlib
import Definitions.Def_ChapterSirkBandLedger
open BookProof.SirkBandLedger















open BookProof.SirkCertificateReader
open BookProof.BandEnclosure



































open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]




open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert BookProof.FriedrichsExtension

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger_lo_zero (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn (finiteModeDomain b) H)
    (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x)
    {L : List BandRecord} (hwf : LedgerWf L)
    (hritz : ∀ m, ritzInf H (galerkinSpan b (m + 1)) ∈
      Set.Icc (ledgerLo L m) (ledgerHi L m)) :
    ledgerLo L 0 ≤ ritzInf H (finiteModeDomain b) ∧
      ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (S : F →L[ℂ] F),
        IsPositiveSelfAdjointExtension H A ∧ IsShiftInvert A 1 S ∧ IsSelfAdjoint S ∧
          ∀ y : Dom, ledgerLo L 0 * ‖(y : F)‖ ^ 2 ≤ quadForm A y := by sorry
