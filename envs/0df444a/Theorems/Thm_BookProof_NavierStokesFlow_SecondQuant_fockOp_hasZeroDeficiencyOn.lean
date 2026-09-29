-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockOp_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockOp_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:39:00.129247+00:00
-- url     : https://prove2.me/theorems/cd246d37-7f5d-4bd9-8439-45862b93b747
-- title:
--   (A : ∀ m, D m →ₗ[ℂ] D m) (hA : ∀ m, HasZeroDeficiencyOn (D m) (A m)) : HasZeroDeficiencyOn (fockCore D) (fockOp A)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockOp_hasZeroDeficiencyOn` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSecondQuant.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesSecondQuant
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant









open scoped ENNReal



variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]





variable (D : ∀ m, Submodule ℂ (S m))


variable {D}

theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_hasZeroDeficiencyOn (A : ∀ m, D m →ₗ[ℂ] D m)
    (hA : ∀ m, HasZeroDeficiencyOn (D m) (A m)) :
    HasZeroDeficiencyOn (fockCore D) (fockOp A) := by sorry
