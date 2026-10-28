-- Prove2me | Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_coeff_zero
-- name    : D1Bound5.bennettPolynomialResidue_residual_coeff_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:31.268493+00:00
-- url     : https://prove2.me/theorems/008a94af-2e40-4f9d-ae80-ebedeceb4537
-- title:
--   Bennett Polynomial Residue residual coeff zero
-- statement:
--   The genuine Bennett residual has a zero of order at least `card I * k`. The cancellation is deduced from exact partial fractions, not assumed.
-- source:
--   D1Bound5/BennettResidualCancellation.lean, lines 59-104, SHA-256 0e8f4d1dac16aef29c7622ad8fa6e48d05646e38a9ebaf133da673991996797d. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.bennettPolynomialResidue_residual_coeff_zero
    (a : I → F) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν : F) (i : I) (r : ℕ) (hr : r < Fintype.card I * k) :
    PowerSeries.coeff r
      (∑ j, (bennettPolynomialResidue Finset.univ a k ν i j : PowerSeries F) *
        PowerSeries.rescale (a j) (PowerSeries.binomialSeries F ν)) = 0 := by sorry









end Nodes

end D1Bound5
end
