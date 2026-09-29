-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockOp_apply
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:58:49.710207+00:00
-- url     : https://prove2.me/theorems/9940df8f-c61d-4c4b-a695-f7c6beee2fa6
-- title:
--   (A : ∀ m, D m →ₗ[ℂ] D m) (f : fockCore D) (m : ι) : ((fockOp A f : lp S 2) : ∀ m, S m) m = ((A m ⟨(f : lp S 2) m, (f.2).2 m⟩ : D m) : S m)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockOp_apply` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSecondQuant.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_apply
import Mathlib
import Definitions.Def_ChapterNavierStokesSecondQuant
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant









open scoped ENNReal



variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]





variable (D : ∀ m, Submodule ℂ (S m))


variable {D}

theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_apply (A : ∀ m, D m →ₗ[ℂ] D m) (f : fockCore D) (m : ι) :
    ((fockOp A f : lp S 2) : ∀ m, S m) m = ((A m ⟨(f : lp S 2) m, (f.2).2 m⟩ : D m) : S m) := by sorry
