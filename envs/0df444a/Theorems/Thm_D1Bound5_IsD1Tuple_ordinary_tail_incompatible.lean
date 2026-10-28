-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_ordinary_tail_incompatible
-- name    : D1Bound5.IsD1Tuple.ordinary_tail_incompatible
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:37:07.318928+00:00
-- url     : https://prove2.me/theorems/981e3a73-ceff-4972-8eee-8a24e37cf7c5
-- title:
--   Is D1Tuple — ordinary tail incompatible
-- statement:
--   The ordinary tail is genuinely infinite. A single checked overlap at orders 5 and 6 propagates because the actual quadratic lower rate exceeds the height rate; geometric lower endpoints are unbounded.
-- source:
--   D1Bound5/OrdinaryClosedIntervals.lean, lines 135-205, SHA-256 2a5f04eb6285acfb92a512be32794797bc3bc72ea1071063ed81f784bc551a9b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Order.Archimedean.Real.Basic
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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OrdinaryClosedIntervals_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5












theorem _root_.D1Bound5.IsD1Tuple.ordinary_tail_incompatible
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 4 → 𝓞 K) (ht : IsD1Tuple t)
    (hAB : ‖phi (t 0 : K)‖ ≤ ‖phi (t 1 : K)‖)
    (hAC : 1000 ≤ ‖phi (t 0 : K)‖*‖phi (t 2 : K)‖)
    (hC : 4*‖phi (t 1 : K)‖ < ‖phi (t 2 : K)‖)
    (hCD : ‖phi (t 2 : K)‖ ≤ ‖phi (t 3 : K)‖)
    (hrate : 42*‖phi (t 1 : K)‖^3*‖phi (t 2 : K)‖ <
      2*‖phi (t 0 : K)‖*‖phi (t 2 : K)‖^2/(5*‖phi (t 1 : K)‖))
    (hoverlap : ordinaryWindowLower ‖phi (t 1 : K)‖ ‖phi (t 2 : K)‖ 6 ≤
      ordinaryWindowUpper ‖phi (t 0 : K)‖ ‖phi (t 1 : K)‖ ‖phi (t 2 : K)‖ 5)
    (hstart : ordinaryWindowLower ‖phi (t 1 : K)‖ ‖phi (t 2 : K)‖ 5 ≤
      ‖phi (t 3 : K)‖) : False := by sorry

end D1Bound5
end
