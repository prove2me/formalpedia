-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finiteQ_inequality
-- name    : D1Bound5.full_ring_finiteQ_inequality
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:07:48.492624+00:00
-- url     : https://prove2.me/theorems/d06e04fc-767c-4303-9f83-3d726744cdb8
-- title:
--   Full ring finite Q inequality
-- statement:
--   The actual finite Q family on six distinct full-ring tuple entries gives its numerical form inequality. Root signs, a nonzero row, integrality, height, and the convergent residual estimate are all obtained in the proof.
-- source:
--   D1Bound5/FiniteQFullRing.lean, lines 8-101, SHA-256 3b4b04c21798d328daae1a9ca05b1a3af8fb181a13b9ea165ed60dc00c3f7890. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
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
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
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


theorem _root_.D1Bound5.full_ring_finiteQ_inequality
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {S : Finset (𝓞 K)} (hS : IsD1 S) (a : Fin 4 → 𝓞 K) (c d : 𝓞 K)
    (haS : ∀ j, a j ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hinj : Function.Injective a) (hac : ∀ j, a j ≠ c)
    (had : ∀ j, a j ≠ d) (hcd : c ≠ d)
    (A T : ℝ) (hA : 0 < A)
    (hlower : ∀ j, A ≤ ‖phi (a j : K)‖)
    (hupper : ∀ j, ‖phi (a j : K)‖ ≤ T)
    (hCT : 4*T ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖)
    (hAC : 1000 ≤ A*‖phi (c : K)‖) :
    ∃ z : 𝓞 K, z^2 = c*d+1 ∧
      1 < 55*T^3*‖phi (c : K)‖^2/‖phi (z : K)‖ +
        3*T*‖phi (z : K)‖/(2*A^2*‖phi (c : K)‖^4) := by sorry

end D1Bound5
end
