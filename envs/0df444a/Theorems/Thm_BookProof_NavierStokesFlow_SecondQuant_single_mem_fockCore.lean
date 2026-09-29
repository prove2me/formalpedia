-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_single_mem_fockCore
-- name    : BookProof.NavierStokesFlow.SecondQuant.single_mem_fockCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T12:00:41.837877+00:00
-- url     : https://prove2.me/theorems/1b575aa5-6c10-46d9-97ad-3808d496d28f
-- title:
--   [DecidableEq ι] (m : ι) (x : S m) (hx : x ∈ D m) : lp.single 2 m x ∈ fockCore D
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.single_mem_fockCore` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSecondQuant.lean — theorem BookProof.NavierStokesFlow.SecondQuant.single_mem_fockCore
import Mathlib
import Definitions.Def_ChapterNavierStokesSecondQuant
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant









open scoped ENNReal



variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]





variable (D : ∀ m, Submodule ℂ (S m))


variable {D}

theorem BookProof.NavierStokesFlow.SecondQuant.single_mem_fockCore [DecidableEq ι] (m : ι) (x : S m) (hx : x ∈ D m) :
    lp.single 2 m x ∈ fockCore D := by sorry
