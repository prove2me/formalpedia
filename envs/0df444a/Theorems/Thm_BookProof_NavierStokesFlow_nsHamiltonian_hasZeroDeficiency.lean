-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsHamiltonian_hasZeroDeficiency
-- name    : BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiency
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:25:49.131974+00:00
-- url     : https://prove2.me/theorems/708332c1-17a3-4c6c-bb9b-617b4f04cef3
-- title:
--   The Lean 4 theorem `nsHamiltonian_hasZeroDeficiency` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsHamiltonian_hasZeroDeficiency` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiency
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)
variable {n : ℕ} (d : NSTruncation n)
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiency :
    HasZeroDeficiency (Matrix.toEuclideanLin (nsHamiltonian d)) := by sorry
