-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsHamiltonian_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:41:23.787274+00:00
-- url     : https://prove2.me/theorems/55558572-e94b-4284-8878-a4f3afa31273
-- title:
--   The Lean 4 theorem `nsHamiltonian_hasZeroDeficiencyOn` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsHamiltonian_hasZeroDeficiencyOn` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow

variable {E : Type*} [AddCommGroup E] [Module ℂ E] {ι : Type*} [Fintype ι]
variable {n : ℕ} (L : LagrangianNS n)
variable {n : ℕ} (d : NSTruncation n)
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
      (restrictToTop (Matrix.toEuclideanLin (nsHamiltonian d))) := by sorry
