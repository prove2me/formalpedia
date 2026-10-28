-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoClearedMatrix_det_ne_zero
-- name    : D1Bound5.bennettTwoClearedMatrix_det_ne_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:19:39.624916+00:00
-- url     : https://prove2.me/theorems/2e8d86c2-0112-46b2-acd0-7a6560d0feb4
-- title:
--   Bennett Two Cleared Matrix det ne zero
-- statement:
--   Nonsingularity of the actual integral two-anchor matrix. All of its ingredients are constructed explicitly; no determinant certificate is input.
-- source:
--   D1Bound5/BennettTwoIntegralMatrix.lean, lines 20-43, SHA-256 136894d1b4f549edd11ad783443c9dfcdff9dc56c2e0bd789e83020f9f2279d2. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoIntegralMatrix_Definitions

section
namespace D1Bound5

variable {F : Type*} [Field F] [CharZero F]






theorem _root_.D1Bound5.bennettTwoClearedMatrix_det_ne_zero
    (a b c : F) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (k : ℕ) (hk : 1 ≤ k) : (bennettTwoClearedMatrix a b c k).det ≠ 0 := by sorry

end D1Bound5
end
