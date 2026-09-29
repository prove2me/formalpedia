-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_SecondQuant_fockComparison_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.SecondQuant.fockComparison_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T13:09:16.691476+00:00
-- url     : https://prove2.me/theorems/4fcd0fe6-0e96-4364-b925-fc92141eb79d
-- title:
--   (d : ℕ) (p q : Fin d → ℕ → ℝ) : HasZeroDeficiencyOn (fockCore fiberCore) (fockComparison d p q)
-- statement:
--   Lean 4 theorem `BookProof.NavierStokesFlow.SecondQuant.fockComparison_hasZeroDeficiencyOn` (module `BookProof.NavierStokesFlow`), source chapter `BookProof/ChapterNavierStokesFlow.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFockFarisLavine.lean — theorem BookProof.NavierStokesFlow.SecondQuant.fockComparison_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SecondQuant








open scoped ENNReal



open FarisLavineLift

variable {ι : Type*}
variable {S : ι → Type*} [∀ m, NormedAddCommGroup (S m)] [∀ m, InnerProductSpace ℂ (S m)]
variable {D : ∀ m, Submodule ℂ (S m)}



















open FarisLavineLift LpNat DiagonalEsa

theorem BookProof.NavierStokesFlow.SecondQuant.fockComparison_hasZeroDeficiencyOn (d : ℕ) (p q : Fin d → ℕ → ℝ) :
    HasZeroDeficiencyOn (fockCore fiberCore) (fockComparison d p q) := by sorry
