-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_secondDerivativeField_momentum
-- name    : BookProof.NavierStokesFlow.secondDerivativeField_momentum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:28:43.265988+00:00
-- url     : https://prove2.me/theorems/45d696e0-b614-48ca-bc53-db4b675ef899
-- title:
--   The Lean 4 theorem `secondDerivativeField_momentum` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `secondDerivativeField_momentum` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.secondDerivativeField_momentum
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.secondDerivativeField_momentum (i j k l m n : Fin 3)
    (p : MvPolynomial (Fin 3 × Fin 3 × Fin 3) ℂ) :
    (MvPolynomial.pderiv (l, m, n)) (MvPolynomial.X (i, j, k) * p)
      - MvPolynomial.X (i, j, k) * (MvPolynomial.pderiv (l, m, n)) p
      = (if l = i ∧ m = j ∧ n = k then p else 0) := by sorry
