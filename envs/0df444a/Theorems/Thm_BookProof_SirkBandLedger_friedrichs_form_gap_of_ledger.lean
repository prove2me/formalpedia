-- Prove2me | Theorems.Thm_BookProof_SirkBandLedger_friedrichs_form_gap_of_ledger
-- name    : BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:13:21.082766+00:00
-- url     : https://prove2.me/theorems/6a291179-fbfa-4a47-86a0-274dff94d0a5
-- title:
--   (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn (finiteModeDomain b) H) (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x) {L : List BandRecord} (hwf...
-- statement:
--   Lean 4 theorem `BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger` (module `BookProof.SirkBandLedger`), source chapter `BookProof/ChapterSirkBandLedger.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterSirkBandLedger.lean

-- Generated from ChapterSirkBandLedger.lean — theorem BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger
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

theorem BookProof.SirkBandLedger.friedrichs_form_gap_of_ledger (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn (finiteModeDomain b) H)
    (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x)
    {L : List BandRecord} (hwf : LedgerWf L)
    (hritz : ∀ m, ritzInf H (galerkinSpan b (m + 1)) ∈
      Set.Icc (ledgerLo L m) (ledgerHi L m))
    {mu : ℝ} {m₀ : ℕ} (hlo : mu ≤ ledgerLo L m₀) :
    (∀ m, ritzInf H (finiteModeDomain b) ∈ Set.Icc (ledgerLo L m) (ledgerHi L m)) ∧
      mu ≤ ritzInf H (finiteModeDomain b) ∧
      ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (S : F →L[ℂ] F),
        IsPositiveSelfAdjointExtension H A ∧ IsShiftInvert A 1 S ∧ IsSelfAdjoint S ∧
          ∀ y : Dom, mu * ‖(y : F)‖ ^ 2 ≤ quadForm A y := by sorry
