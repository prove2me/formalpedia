-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockOp_isSymmetricDom
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockOp_isSymmetricDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:12:41.411588+00:00
-- url     : https://prove2.me/theorems/dbc5e1e7-2e4c-4a98-bf43-b7a813bf9893
-- title:
--   (A : ∀ m, D m →ₗ[ℂ] D m) (hA : ∀ m, FullEsa.IsSymmetricDom (A m)) : FullEsa.IsSymmetricDom (fockOp A)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockOp_isSymmetricDom` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockFarisLavine.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_isSymmetricDom
import Mathlib
import Definitions.Def_ChapterNavierStokesFockFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant








open scoped ENNReal



open FarisLavineLift

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}

theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_isSymmetricDom (A : ∀ m, D m →ₗ[ℂ] D m)
    (hA : ∀ m, FullEsa.IsSymmetricDom (A m)) :
    FullEsa.IsSymmetricDom (fockOp A) := by sorry
