-- Prove2me | Theorems.Thm_BookProof_BandEnclosure_friedrichs_form_gap_of_nested_ritz_bands
-- name    : BookProof.BandEnclosure.friedrichs_form_gap_of_nested_ritz_bands
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T08:00:56.355283+00:00
-- url     : https://prove2.me/theorems/622935df-5848-4de3-8724-a9c795839f12
-- title:
--   (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn (finiteModeDomain b) H) (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x) {lo hi : ℕ → ℝ} {mu...
-- statement:
--   Lean 4 theorem `BookProof.BandEnclosure.friedrichs_form_gap_of_nested_ritz_bands` (module `BookProof.BandEnclosure`), source chapter `BookProof/ChapterBandEnclosure.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterBandEnclosure.lean

-- Generated from ChapterBandEnclosure.lean — theorem BookProof.BandEnclosure.friedrichs_form_gap_of_nested_ritz_bands
import Mathlib
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterFriedrichsFormGap
open BookProof.BandEnclosure










noncomputable section

open Filter Topology


open BookProof.FockOneParticleGap BookProof.FockSecondQuantization
open BookProof.ChapterH6 BookProof.ChapterH8















open BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.YangMillsFriedrichsLimit BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]













open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert BookProof.FriedrichsExtension
open BookProof.FriedrichsFormGap

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.BandEnclosure.friedrichs_form_gap_of_nested_ritz_bands (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn (finiteModeDomain b) H)
    (hpos : ∀ x : finiteModeDomain b, 0 ≤ quadForm H x)
    {lo hi : ℕ → ℝ} {mu : ℝ} (hnest : NestedBands lo hi)
    (hritz : ∀ m, ritzInf H (galerkinSpan b (m + 1)) ∈ Set.Icc (lo m) (hi m))
    {m₀ : ℕ} (hlo : mu ≤ lo m₀) :
    (∀ m, ritzInf H (finiteModeDomain b) ∈ Set.Icc (lo m) (hi m)) ∧
      mu ≤ ritzInf H (finiteModeDomain b) ∧
      ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F) (S : F →L[ℂ] F),
        IsPositiveSelfAdjointExtension H A ∧ IsShiftInvert A 1 S ∧ IsSelfAdjoint S ∧
          ∀ y : Dom, mu * ‖(y : F)‖ ^ 2 ≤ quadForm A y := by sorry
