-- Prove2me | Theorems.Thm_D1Bound5_bennettTwoRowForm_norm_lt
-- name    : D1Bound5.bennettTwoRowForm_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:23:01.811144+00:00
-- url     : https://prove2.me/theorems/81bb4328-a78e-4959-8985-894e393816de
-- title:
--   Bennett Two Row Form norm lt
-- statement:
--   The actual determinant row, coefficient bounds, and residual bound give the manuscript's all-order upper estimate once the two root errors have been produced. The following full-ring theorem produces them.
-- source:
--   D1Bound5/BennettRootTransfer.lean, lines 59-123, SHA-256 a38bf0ffc8b2ba8c102ba5867c75b61a824a8d23c6fce61a35bfcc498b7a884a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_D1Bound5_BennettIntegralRowSelection_Definitions
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.bennettTwoRowForm_norm_lt
    (a b c z sA sB : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hab : a ≠ b) (hz : z ≠ 0)
    (hAB : ‖a‖ ≤ ‖b‖) (hAC : 1000 ≤ ‖a‖ * ‖c‖)
    (herrorA : ‖(1 + 1 / (a * c)) ^ (1 / 2 : ℂ) - sA / (a * z)‖ <
      (3 / 2 : ℝ) * ‖c‖ / (‖a‖ * ‖z‖ ^ 2))
    (herrorB : ‖(1 + 1 / (b * c)) ^ (1 / 2 : ℂ) - sB / (b * z)‖ <
      (3 / 2 : ℝ) * ‖c‖ / (‖b‖ * ‖z‖ ^ 2))
    (k : ℕ) (hk : 1 ≤ k) (i : Fin 3) :
    ‖bennettTwoRowForm a b c z sA sB k i‖ <
      3 * ‖c‖ * (42 * ‖b‖ ^ 3 * ‖c‖) ^ k / (‖b‖ * ‖z‖) +
        ‖z‖ / (2 * (bennettTwoResidualRate ‖a‖ ‖b‖ ‖c‖ ‖a - b‖) ^ k) := by sorry



end D1Bound5
end
