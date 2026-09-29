-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsHamiltonian_hasZeroDeficiencyOn_of_flow
-- name    : BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn_of_flow
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:53:33.592265+00:00
-- url     : https://prove2.me/theorems/dedaa307-ee1f-4cb9-8b51-8fdf1ab6dc40
-- title:
--   The Lean 4 theorem `nsHamiltonian_hasZeroDeficiencyOn_of_flow` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsHamiltonian_hasZeroDeficiencyOn_of_flow` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn_of_flow
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite














variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn_of_flow :
    HasZeroDeficiencyOn (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
      (restrictToTop (Matrix.toEuclideanLin (nsHamiltonian d))) := by sorry
