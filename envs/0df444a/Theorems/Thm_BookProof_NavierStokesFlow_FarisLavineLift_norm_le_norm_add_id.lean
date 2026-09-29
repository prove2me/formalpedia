-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_norm_le_norm_add_id
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.norm_le_norm_add_id
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:24:20.110473+00:00
-- url     : https://prove2.me/theorems/da816e7c-e05e-4687-86c2-c52f1d927767
-- title:
--   (N : D →ₗ[ℂ] D) (v : D) (hpos : 0 ≤ (inner ℂ ((N v : D) : F) ((v : F)) : ℂ).re) : ‖((N v : D) : F)‖ ≤ ‖((((N + LinearMap.id : D →ₗ[ℂ] D)) v : D) : F)‖
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.norm_le_norm_add_id` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_le_norm_add_id
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem BookProof.NavierStokesFlow.FarisLavineLift.norm_le_norm_add_id (N : D →ₗ[ℂ] D) (v : D)
    (hpos : 0 ≤ (inner ℂ ((N v : D) : F) ((v : F)) : ℂ).re) :
    ‖((N v : D) : F)‖ ≤ ‖((((N + LinearMap.id : D →ₗ[ℂ] D)) v : D) : F)‖ := by sorry
