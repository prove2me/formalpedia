-- Prove2me | Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_dvd
-- name    : D1Bound5.bennettPolynomialResidue_residual_dvd
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:33:46.135186+00:00
-- url     : https://prove2.me/theorems/fe28d961-455c-4be5-8df4-9acb7d6106a9
-- title:
--   Bennett Polynomial Residue residual dvd
-- statement:
--   Polynomial form of the actual residual cancellation, suitable for the column-replacement determinant argument.
-- source:
--   D1Bound5/BennettResidualCancellation.lean, lines 119-143, SHA-256 0e8f4d1dac16aef29c7622ad8fa6e48d05646e38a9ebaf133da673991996797d. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]






theorem _root_.D1Bound5.bennettPolynomialResidue_residual_dvd
    (a : I → F) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν : F) (i : I) :
    (Polynomial.X : Polynomial F) ^ (Fintype.card I * k) ∣
      ∑ j, PowerSeries.trunc (Fintype.card I * k)
        (PowerSeries.rescale (a j) (PowerSeries.binomialSeries F ν)) *
          bennettPolynomialResidue Finset.univ a k ν i j := by sorry





end Nodes

end D1Bound5
end
