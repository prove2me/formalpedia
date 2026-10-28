-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finiteN2_inequalities
-- name    : D1Bound5.full_ring_finiteN2_inequalities
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:08:00.249415+00:00
-- url     : https://prove2.me/theorems/896658d6-3712-49ae-8623-c9c6e0bbda6f
-- title:
--   Full ring finite N2 inequalities
-- statement:
--   Both the table and distance-sensitive N2 inequalities for four actual full-ring tuple entries. Every coefficient, residual, determinant, integral row and root sign is constructed in the preceding theorems.
-- source:
--   D1Bound5/FiniteN2FullRing.lean, lines 9-94, SHA-256 9fba1c6227dfee05d356c23b7a3648dd86746ebe3a529718434bfb6a9b638e48. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_IsD1

section
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.full_ring_finiteN2_inequalities
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {S : Finset (𝓞 K)} (hS : IsD1 S) (x y c d : 𝓞 K)
    (hxS : x ∈ S) (hyS : y ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hxy : x ≠ y) (hxc : x ≠ c) (hyc : y ≠ c)
    (hxd : x ≠ d) (hyd : y ≠ d) (hcd : c ≠ d)
    (hXY : ‖phi (x : K)‖ ≤ ‖phi (y : K)‖)
    (hXC : 1000 ≤ ‖phi (x : K)‖*‖phi (c : K)‖)
    (hCY : 200*‖phi (y : K)‖ ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖) :
    ∃ z : 𝓞 K, z^2 = c*d+1 ∧
      (1 < 243*‖phi (y : K)‖^4*‖phi (c : K)‖^3/‖phi (z : K)‖ +
        (5/4 : ℝ)*‖phi (y : K)‖^2*‖phi (z : K)‖ /
          (‖phi (x : K)‖^3*‖phi (c : K)‖^4)) ∧
      (1 < 243*‖phi (y : K)‖^4*‖phi (c : K)‖^3/‖phi (z : K)‖ +
        (101/2560 : ℝ)*max (‖phi (x : K)-phi (y : K)‖^4)
          (‖phi (x : K)‖*‖phi (x : K)-phi (y : K)‖^3)*‖phi (z : K)‖ /
            (‖phi (x : K)‖^3*‖phi (y : K)‖^2*‖phi (c : K)‖^4)) := by sorry

end D1Bound5
end
