-- Prove2me | Theorems.Thm_BookProof_FockSecondQuantization_sum_creVec_annA_subset
-- name    : BookProof.FockSecondQuantization.sum_creVec_annA_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T12:14:35.555848+00:00
-- url     : https://prove2.me/theorems/54b51ce2-6f7e-47ac-ac56-72d02706ed30
-- title:
--   (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) {K L : Finset ℕ} (hKL : K ⊆ L) (hK : modes u ⊆ K) : ∑ k ∈ K, creVec (col k) (annA k u) = ∑ k ∈ L, creVec (col k) (annA k u)
-- statement:
--   Lean 4 theorem `BookProof.FockSecondQuantization.sum_creVec_annA_subset` (module `BookProof.FockSecondQuantization`), source chapter `BookProof/ChapterFockSecondQuantization.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterFockSecondQuantization.lean

-- Generated from ChapterFockSecondQuantization.lean — theorem BookProof.FockSecondQuantization.sum_creVec_annA_subset
import Mathlib
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockSecondQuantization







open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section

theorem BookProof.FockSecondQuantization.sum_creVec_annA_subset (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) {K L : Finset ℕ}
    (hKL : K ⊆ L) (hK : modes u ⊆ K) :
    ∑ k ∈ K, creVec (col k) (annA k u) = ∑ k ∈ L, creVec (col k) (annA k u) := by sorry
