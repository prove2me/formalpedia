-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_norm_inner_commutator_sum_le
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T07:56:18.884023+00:00
-- url     : https://prove2.me/theorems/b96391f9-c91d-427b-a832-5fa3e001541d
-- title:
--   (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D)) (c₂ : ℝ) (hc₂ : 0 ≤ c₂) (v : D) (hcomm : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → (h k).comp (n l) = (n l).comp (h k)) (hbound : ∀ k ∈...
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D)) (c₂ : ℝ)
    (hc₂ : 0 ≤ c₂) (v : D)
    (hcomm : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → (h k).comp (n l) = (n l).comp (h k))
    (hbound : ∀ k ∈ s, ‖(inner ℂ ((v : F)) ((commDom (h k) (n k) v : D) : F) : ℂ)‖
      ≤ c₂ * (inner ℂ ((v : F)) ((n k v : D) : F) : ℂ).re) :
    ‖(inner ℂ ((v : F))
        ((commDom (∑ k ∈ s, h k) ((∑ k ∈ s, n k) + LinearMap.id) v : D) : F) : ℂ)‖
      ≤ c₂ * (inner ℂ ((v : F))
        ((((∑ k ∈ s, n k) + LinearMap.id : D →ₗ[ℂ] D) v : D) : F) : ℂ).re := by sorry
