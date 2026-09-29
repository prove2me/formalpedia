-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockOp_sub
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockOp_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:13:58.222659+00:00
-- url     : https://prove2.me/theorems/0b6c6d6f-7b85-46df-80fe-20791d9efd41
-- title:
--   (A B : ∀ m, D m →ₗ[ℂ] D m) : fockOp (fun m => A m - B m) = fockOp A - fockOp B
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockOp_sub` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockFarisLavine.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_sub
import Mathlib
import Definitions.Def_ChapterNavierStokesFockFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant








open scoped ENNReal



open FarisLavineLift

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}

theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_sub (A B : ∀ m, D m →ₗ[ℂ] D m) :
    fockOp (fun m => A m - B m) = fockOp A - fockOp B := by sorry
