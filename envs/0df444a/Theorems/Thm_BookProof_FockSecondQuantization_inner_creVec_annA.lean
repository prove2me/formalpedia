-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_inner_creVec_annA
-- name    : BookProof.FockSecondQuantization.inner_creVec_annA
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:15:50.792983+00:00
-- url     : https://prove2.me/theorems/937fb40d-9554-4c55-8059-5b0f7ef359a6
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) (k : ℕ) {L : Finset ℕ} (h : (col k).support ⊆ L) : (inner ℂ (toLp (creVec (col k) (annA k u))) (toLp v) : ℂ) = ∑ j ∈ L,...
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.inner_creVec_annA` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.inner_creVec_annA
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.inner_creVec_annA (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) (k : ℕ) {L : Finset ℕ}
    (h : (col k).support ⊆ L) :
    (inner ℂ (toLp (creVec (col k) (annA k u))) (toLp v) : ℂ)
      = ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
          * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by sorry
