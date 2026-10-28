-- Prove2me | Theorems.Thm_D1Bound5_bennettDirectedProduct_ne_zero
-- name    : D1Bound5.bennettDirectedProduct_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:11.814895+00:00
-- url     : https://prove2.me/theorems/1a09bbb4-7ec1-4ce2-bb7d-f07df03068cc
-- title:
--   Bennett Directed Product ne zero
-- statement:
--   Distinct nodes make every directed reciprocal-difference factor nonzero.
-- source:
--   D1Bound5/BennettDeterminantNonzero.lean, lines 18-29, SHA-256 164557a33c15c3cbb3b959546eec9a30e4643b3c84fcd2c4978c868aa62a1f8f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettDeterminantFormula_Definitions

section
open Finset

namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]




theorem _root_.D1Bound5.bennettDirectedProduct_ne_zero {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → F) (ha : Function.Injective a) (k : ℕ) :
    bennettDirectedProduct a k ≠ 0 := by sorry





end D1Bound5
end
