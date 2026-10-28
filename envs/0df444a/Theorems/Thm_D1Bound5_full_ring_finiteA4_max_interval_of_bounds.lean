-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finiteA4_max_interval_of_bounds
-- name    : D1Bound5.full_ring_finiteA4_max_interval_of_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:32:48.951714+00:00
-- url     : https://prove2.me/theorems/e720e55d-fd47-4e8a-8d94-8b0ce9899e0e
-- title:
--   Full ring finite A4 max interval of bounds
-- statement:
--   The complete distance-sensitive A4 window from proved actual coefficients and the explicit maximum-distance bound. Every anchor power is preserved in the upper endpoint; roots, signs, and nonzero row selection are constructed.
-- source:
--   D1Bound5/FiniteA4MaxInterval.lean, lines 8-83, SHA-256 93fa744723af6ab88a28f574a1e9e4cdd65a5d5887461a047564751ed80d6af7. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteA4Matrix_Definitions
import Definitions.Def_D1Bound5_IsD1

section
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.full_ring_finiteA4_max_interval_of_bounds
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {S : Finset (𝓞 K)} (hS : IsD1 S) (x y c d : 𝓞 K)
    (hxS : x ∈ S) (hyS : y ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hxy : x ≠ y) (hxc : x ≠ c) (hyc : y ≠ c)
    (hxd : x ≠ d) (hyd : y ≠ d) (hcd : c ≠ d)
    (hXY : ‖phi (x : K)‖ ≤ ‖phi (y : K)‖)
    (hC1000 : 1000 ≤ ‖phi (c : K)‖)
    (hCY : 200*‖phi (y : K)‖ ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖)
    (M R : ℝ) (hM : 0 < M) (hRpos : 0 < R)
    (hheight : ∀ i : Fin 3,
      (101/100 : ℝ)*(‖finiteA4Left (phi (x : K)) (phi (y : K)) (phi (c : K)) i‖+
        ‖finiteA4Right (phi (x : K)) (phi (y : K)) (phi (c : K)) i‖) <
          M*‖phi (y : K)‖^9*‖phi (c : K)‖^4)
    (hR : (6363/409600 : ℝ)*max (‖phi (x : K)-phi (y : K)‖^8)
      (‖phi (x : K)‖*‖phi (x : K)-phi (y : K)‖^7) ≤ R*‖phi (y : K)‖^8)
    (hleft : 4*M^2*‖phi (y : K)‖^18*‖phi (c : K)‖^9/
      (1-1/4000 : ℝ) ≤ ‖phi (d : K)‖)
    (hright : ‖phi (d : K)‖ ≤ ‖phi (x : K)‖^10*‖phi (c : K)‖^13/
      (4*R^2*‖phi (y : K)‖^8*(1+1/4000 : ℝ))) : False := by sorry

end D1Bound5
end
