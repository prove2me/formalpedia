-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockOp_single
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockOp_single
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-13T10:02:48.331134+00:00
-- url     : https://prove2.me/theorems/97e09685-eb5d-4833-a3e5-459d6eb48973
-- title:
--   The Lean 4 theorem `fockOp_single` in the `ChapterNavierStokesSecondQuant` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fockOp_single` in the `ChapterNavierStokesSecondQuant` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesSecondQuant.lean

-- Generated from ChapterNavierStokesSecondQuant.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_single
import Mathlib
import Definitions.Def_ChapterNavierStokesSecondQuant
import Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_single_mem_fockCore
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant









open scoped ENNReal



variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]





variable (D : ∀ m, Submodule ℂ (S m))


variable {D}

theorem BookProof.NavierStokesFlow.SecondQuant.fockOp_single [DecidableEq ι] (A : ∀ m, D m →ₗ[ℂ] D m) (m : ι) (x : D m) :
    (fockOp A ⟨lp.single 2 m (x : S m), single_mem_fockCore m (x : S m) x.2⟩ : lp S 2)
      = lp.single 2 m ((A m x : D m) : S m) := by sorry
