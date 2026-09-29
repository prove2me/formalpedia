-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockCore_dense
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockCore_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:38:19.042653+00:00
-- url     : https://prove2.me/theorems/c3b58e35-7ff6-4c12-8129-6e0870a346e8
-- title:
--   (hD : ∀ m, Dense ((D m : Submodule ℂ (S m)) : Set (S m))) : Dense ((fockCore D : Submodule ℂ (lp S 2)) : Set (lp S 2))
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockCore_dense` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesSecondQuant.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockCore_dense
import Mathlib
import Definitions.Def_ChapterNavierStokesSecondQuant
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant









open scoped ENNReal



variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]





variable (D : ∀ m, Submodule ℂ (S m))


variable {D}

theorem BookProof.NavierStokesFlow.SecondQuant.fockCore_dense (hD : ∀ m, Dense ((D m : Submodule ℂ (S m)) : Set (S m))) :
    Dense ((fockCore D : Submodule ℂ (lp S 2)) : Set (lp S 2)) := by sorry
