-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_coe_sum_apply
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.coe_sum_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:47:16.63643+00:00
-- url     : https://prove2.me/theorems/0fb1007e-70cd-4c32-9d7a-b925824e23df
-- title:
--   (s : Finset κ) (A : κ → (D →ₗ[ℂ] D)) (v : D) : (((∑ k ∈ s, A k) v : D) : F) = ∑ k ∈ s, ((A k v : D) : F)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.coe_sum_apply` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.coe_sum_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem BookProof.NavierStokesFlow.FarisLavineLift.coe_sum_apply (s : Finset κ) (A : κ → (D →ₗ[ℂ] D)) (v : D) :
    (((∑ k ∈ s, A k) v : D) : F) = ∑ k ∈ s, ((A k v : D) : F) := by sorry
