-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsHamiltonian_ne_zero_example
-- name    : BookProof.NavierStokesFlow.nsHamiltonian_ne_zero_example
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:30:11.553991+00:00
-- url     : https://prove2.me/theorems/3fec5e66-7d2d-4cee-8da6-f77f7866c56a
-- title:
--   The Lean 4 theorem `nsHamiltonian_ne_zero_example` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsHamiltonian_ne_zero_example` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsHamiltonian_ne_zero_example
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.nsHamiltonian_ne_zero_example :
    nsHamiltonian (nsTruncationOfDiagonal (n := 1) (fun _ _ => 1) (fun _ => 1)
      (fun _ => Matrix.conjTranspose_one) 0) ≠ 0 := by sorry
