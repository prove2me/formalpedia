-- Prove2me | Theorems.Thm_D1Bound5_full_ring_bennett_two_integer_k
-- name    : D1Bound5.full_ring_bennett_two_integer_k
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:06:18.388691+00:00
-- url     : https://prove2.me/theorems/3482389d-98e3-41f1-b71d-be6620004289
-- title:
--   Full ring bennett two integer k
-- statement:
--   The manuscript's two-anchor Bennett inequality for actual roots in the full integer ring of an imaginary quadratic field. Nonsingularity, integrality, the norm lower bound, both approximation bounds, and the nonzero terminal root are derived, not supplied as certificates.
-- source:
--   D1Bound5/BennettRootTransfer.lean, lines 125-188, SHA-256 a38bf0ffc8b2ba8c102ba5867c75b61a824a8d23c6fce61a35bfcc498b7a884a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_BennettTwoResidualRate_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5






theorem _root_.D1Bound5.full_ring_bennett_two_integer_k
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b c d rA rB vA vB z : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hab : a ≠ b)
    (hrA : rA ^ 2 = a * c + 1) (hrB : rB ^ 2 = b * c + 1)
    (hvA : vA ^ 2 = a * d + 1) (hvB : vB ^ 2 = b * d + 1)
    (hzsq : z ^ 2 = c * d + 1)
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖)
    (hAC : 1000 ≤ ‖phi (a : K)‖ * ‖phi (c : K)‖)
    (hC : 4 * ‖phi (b : K)‖ < ‖phi (c : K)‖)
    (k : ℕ) (hk : 1 ≤ k) :
    1 < 3 * ‖phi (c : K)‖ * (42 * ‖phi (b : K)‖ ^ 3 * ‖phi (c : K)‖) ^ k /
        (‖phi (b : K)‖ * ‖phi (z : K)‖) +
      ‖phi (z : K)‖ / (2 * (bennettTwoResidualRate
        ‖phi (a : K)‖ ‖phi (b : K)‖ ‖phi (c : K)‖
          ‖phi (a : K) - phi (b : K)‖) ^ k) := by sorry

end D1Bound5
end
