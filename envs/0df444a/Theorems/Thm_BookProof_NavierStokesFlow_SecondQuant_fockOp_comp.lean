-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockOp_comp
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockOp_comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:11:25.631106+00:00
-- url     : https://prove2.me/theorems/f1eabe72-276e-42c1-a5a1-8684ac78f7a4
-- title:
--   (A B : ∀ m, D m →ₗ[ℂ] D m) : fockOp (fun m => (A m).comp (B m)) = (fockOp A).comp (fockOp B)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockOp_comp` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockFarisLavine.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_comp
import Mathlib
import Definitions.Def_ChapterNavierStokesFockFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant








open scoped ENNReal



open FarisLavineLift

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}

theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_comp (A B : ∀ m, D m →ₗ[ℂ] D m) :
    fockOp (fun m => (A m).comp (B m)) = (fockOp A).comp (fockOp B) := by sorry
