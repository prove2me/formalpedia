-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockCore_ne_top
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockCore_ne_top
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T11:58:07.612383+00:00
-- url     : https://prove2.me/theorems/ec760dcb-0e6a-42b3-bdc1-2ef7b45e5f47
-- title:
--   {S : ℕ → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)] (D : ∀ m, Submodule ℂ (S m)) (v : ∀ m, S m) (hv : ∀ m, ‖v m‖ = 1) : (fockCore D : Submodule ℂ (lp S 2)) ≠ ⊤
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockCore_ne_top` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSecondQuant.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockCore_ne_top
import Mathlib
import Definitions.Def_ChapterNavierStokesSecondQuant
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant









open scoped ENNReal



variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]





variable (D : ∀ m, Submodule ℂ (S m))


variable {D}

theorem BookProof.NavierStokesFlow.SecondQuant.fockCore_ne_top {S : ℕ → Type*} [∀ m, NormedAddCommGroup (S m)]
    [∀ m, InnerProductSpace ℂ (S m)] (D : ∀ m, Submodule ℂ (S m))
    (v : ∀ m, S m) (hv : ∀ m, ‖v m‖ = 1) :
    (fockCore D : Submodule ℂ (lp S 2)) ≠ ⊤ := by sorry
