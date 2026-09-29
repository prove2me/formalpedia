-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_derivativeField_momentum
-- name    : BookProof.NavierStokesFlow.derivativeField_momentum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:34:13.425718+00:00
-- url     : https://prove2.me/theorems/55f2cebf-d9cb-4d83-b57b-fc81afcf36eb
-- title:
--   The Lean 4 theorem `derivativeField_momentum` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `derivativeField_momentum` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.derivativeField_momentum
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.derivativeField_momentum (j k m n : Fin 3) (p : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    (MvPolynomial.pderiv (m, n)) (MvPolynomial.X (j, k) * p)
      - MvPolynomial.X (j, k) * (MvPolynomial.pderiv (m, n)) p
      = (if m = j ∧ n = k then p else 0) := by sorry
