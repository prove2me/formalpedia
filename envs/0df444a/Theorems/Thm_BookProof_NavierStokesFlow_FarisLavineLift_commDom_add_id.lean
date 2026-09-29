-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FarisLavineLift_commDom_add_id
-- name    : BookProof.NavierStokesFlow.FarisLavineLift.commDom_add_id
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:48:01.362042+00:00
-- url     : https://prove2.me/theorems/30426b21-710d-4489-b442-997b873da5cc
-- title:
--   (A B : D →ₗ[ℂ] D) : commDom A (B + LinearMap.id) = commDom A B
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.FarisLavineLift.commDom_add_id` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFarisLavineLift.lean — theorem BookProof.NavierStokesFlow.FarisLavineLift.commDom_add_id
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift













variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)




















variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {κ : Type*}

theorem BookProof.NavierStokesFlow.FarisLavineLift.commDom_add_id (A B : D →ₗ[ℂ] D) :
    commDom A (B + LinearMap.id) = commDom A B := by sorry
