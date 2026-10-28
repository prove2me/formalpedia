-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finiteQ_closed_interval_excluded
-- name    : D1Bound5.full_ring_finiteQ_closed_interval_excluded
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:51:06.91767+00:00
-- url     : https://prove2.me/theorems/8f20dc86-702e-41bb-a928-20621b21170e
-- title:
--   Full ring finite Q closed interval excluded
-- statement:
--   The actual finite Q family excludes the manuscript's entire closed interval, including its endpoints, for six distinct full-ring tuple entries in the stated size range.
-- source:
--   D1Bound5/FiniteQInterval.lean, lines 9-73, SHA-256 93002bc61684705a1dbdf4c53f0dd7e54b963a766cfabd82272bd713d42011b8. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.full_ring_finiteQ_closed_interval_excluded
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
    (hAC : 1000 ≤ A*‖phi (c : K)‖)
    (hleft : 4*55^2*T^6*‖phi (c : K)‖^3/(1-1/4000 : ℝ) ≤ ‖phi (d : K)‖)
    (hright : ‖phi (d : K)‖ ≤
      A^4*‖phi (c : K)‖^7/(9*T^2*(1+1/4000 : ℝ))) : False := by sorry

end D1Bound5
end
