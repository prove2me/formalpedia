-- Prove2me | Theorems.Thm_D1Bound5_bennettPolynomialMatrix_det_monomial
-- name    : D1Bound5.bennettPolynomialMatrix_det_monomial
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:01:12.960571+00:00
-- url     : https://prove2.me/theorems/1c5065aa-7be9-4a72-b08c-2033f82555ee
-- title:
--   Bennett Polynomial Matrix det monomial
-- statement:
--   The determinant of the actual arbitrary-order Bennett matrix is a single monomial. This proves its exact possible degree without assuming residual cancellation; the value and nonvanishing of its coefficient are separate.
-- source:
--   D1Bound5/BennettResidualCancellation.lean, lines 150-171, SHA-256 0e8f4d1dac16aef29c7622ad8fa6e48d05646e38a9ebaf133da673991996797d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettResidualCancellation_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]



section Nodes

variable {I : Type*} [Fintype I] [DecidableEq I]










theorem _root_.D1Bound5.bennettPolynomialMatrix_det_monomial
    (a : I → F) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν : F) (q : I) (hq : a q = 0) :
    (bennettPolynomialMatrix a k ν).det =
      Polynomial.C ((bennettPolynomialMatrix a k ν).det.coeff (Fintype.card I * k)) *
        Polynomial.X ^ (Fintype.card I * k) := by sorry

end Nodes

end D1Bound5
end
