-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_norm_inner_commutator_sum_le_alt
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le_alt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T13:12:24.190659+00:00
-- url     : https://prove2.me/theorems/86a053d3-45a7-4bcb-9e93-07051ac1b6ad
-- title:
--   BookProof.NavierStokesFlow.FarisLavineLift.norm.inner.commutator.sum.le'
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.norm.inner.commutator.sum.le'` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le'
-- NOTE: the source declaration is `norm_inner_commutator_sum_le'`; the platform's
-- `theorem_name` validator rejects a trailing prime (it requires dot-separated
-- identifier segments), so this node is published under the prime-free name
-- `norm_inner_commutator_sum_le_alt`.  The statement is unchanged.
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le_alt (s : Finset κ) (h n : κ → (D →ₗ[ℂ] D)) (c₂ : ℝ)
    (hc₂ : 0 ≤ c₂) (v : D)
    (hcomm : ∀ k ∈ s, ∀ l ∈ s, k ≠ l → (h k).comp (n l) = (n l).comp (h k))
    (hbound : ∀ k ∈ s, ‖(inner ℂ ((v : F)) ((commDom (h k) (n k) v : D) : F) : ℂ)‖
      ≤ c₂ * (inner ℂ ((v : F)) ((n k v : D) : F) : ℂ).re) :
    ‖(inner ℂ ((v : F))
        ((commDom (∑ k ∈ s, h k) ((∑ k ∈ s, n k) + LinearMap.id) v : D) : F) : ℂ)‖
      ≤ c₂ * ‖(inner ℂ ((v : F))
        ((((∑ k ∈ s, n k) + LinearMap.id : D →ₗ[ℂ] D) v : D) : F) : ℂ)‖ := by sorry
