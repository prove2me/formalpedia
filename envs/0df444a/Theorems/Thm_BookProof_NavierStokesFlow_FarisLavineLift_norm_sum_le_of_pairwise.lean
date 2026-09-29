-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_norm_sum_le_of_pairwise
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_le_of_pairwise
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:56:23.267831+00:00
-- url     : https://prove2.me/theorems/47c8ee13-736b-41e0-9f22-9c3f22d7041a
-- title:
--   (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D)) (cst : ℝ) (hc : 0 ≤ cst) (v : D) (hpair : ∀ k ∈ s, ∀ l ∈ s, |(inner ℂ ((h k v : D) : F) ((h l v : D) : F) : ℂ).re| ≤ cst ^ 2 *...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_le_of_pairwise` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_le_of_pairwise
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_le_of_pairwise (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D)) (cst : ℝ)
    (hc : 0 ≤ cst) (v : D)
    (hpair : ∀ k ∈ s, ∀ l ∈ s,
      |(inner ℂ ((h k v : D) : F) ((h l v : D) : F) : ℂ).re|
        ≤ cst ^ 2 * (inner ℂ ((n k v : D) : F) ((n l v : D) : F) : ℂ).re) :
    ‖(((∑ k ∈ s, h k) v : D) : F)‖ ≤ cst * ‖(((∑ k ∈ s, n k) v : D) : F)‖ := by sorry
