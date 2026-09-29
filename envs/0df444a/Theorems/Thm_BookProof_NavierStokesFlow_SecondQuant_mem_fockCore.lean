-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_mem_fockCore
-- name    : BookProof.NavierStokesFlow.SecondQuant.mem_fockCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:59:24.917978+00:00
-- url     : https://prove2.me/theorems/1f4c2e46-4c45-48d4-8538-5761bdc43914
-- title:
--   {f : lp S 2} : f ∈ fockCore D ↔ (Function.support fun m => ‖(f : ∀ m, S m) m‖).Finite ∧ ∀ m, (f : ∀ m, S m) m ∈ D m
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.mem_fockCore` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSecondQuant.lean — theorem BookProof.NavierStokesFlow.SecondQuant.mem_fockCore
import Mathlib
import Definitions.Def_ChapterNavierStokesSecondQuant
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant









open scoped ENNReal



variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]





variable (D : ∀ m, Submodule ℂ (S m))


variable {D}

theorem BookProof.NavierStokesFlow.SecondQuant.mem_fockCore {f : lp S 2} :
    f ∈ fockCore D ↔
      (Function.support fun m => ‖(f : ∀ m, S m) m‖).Finite ∧ ∀ m, (f : ∀ m, S m) m ∈ D m := by sorry
