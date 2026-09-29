-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_commDom_apply
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.commDom_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:48:43.102522+00:00
-- url     : https://prove2.me/theorems/8f3bfa65-9d12-4b62-a273-523c9e16dd30
-- title:
--   (A B : D →ₗ[ℂ] D) (v : D) : commDom A B v = A (B v) - B (A v)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.commDom_apply` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.commDom_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem BookProof.NavierStokesFlow.FarisLavineLift.commDom_apply (A B : D →ₗ[ℂ] D) (v : D) :
    commDom A B v = A (B v) - B (A v) := by sorry
