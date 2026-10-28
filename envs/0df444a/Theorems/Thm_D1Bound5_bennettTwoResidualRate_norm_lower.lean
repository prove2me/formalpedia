-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoResidualRate_norm_lower
-- name    : D1Bound5.bennettTwoResidualRate_norm_lower
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:15.043857+00:00
-- url     : https://prove2.me/theorems/f24acee3-07d2-47fd-81fd-73d8347e82dd
-- title:
--   Bennett Two Residual Rate norm lower
-- statement:
--   Instantiation with the actual anchor norms and their actual complex separation. The separation estimate is derived by the triangle inequality.
-- source:
--   D1Bound5/BennettRateLower.lean, lines 37-46, SHA-256 2a05d2a63514f5a778527c82f79a324a012d2e94fcd2c7bd6c3b5978ca22dd1f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions

section
namespace D1Bound5






theorem _root_.D1Bound5.bennettTwoResidualRate_norm_lower (a b c : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hAB : ‖a‖ ≤ ‖b‖) (hAC : 1000 ≤ ‖a‖ * ‖c‖) :
    2 * ‖a‖ * ‖c‖ ^ 2 / (5 * ‖b‖) <
      bennettTwoResidualRate ‖a‖ ‖b‖ ‖c‖ ‖a - b‖ := by sorry

end D1Bound5
end
