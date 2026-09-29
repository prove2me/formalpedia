-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsHamiltonian_isPolynomial
-- name    : BookProof.NavierStokesFlow.nsHamiltonian_isPolynomial
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:53:06.70444+00:00
-- url     : https://prove2.me/theorems/0369f73b-3ab3-4a3f-a41b-5ad14f28df62
-- title:
--   The Lean 4 theorem `nsHamiltonian_isPolynomial` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsHamiltonian_isPolynomial` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.nsHamiltonian_isPolynomial
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsHamiltonian_isPolynomial :
    nsHamiltonian d = ∑ a : NSWordIndex, nsCoeff d.nu a • ((nsWord a).map (nsGen d)).prod := by sorry
