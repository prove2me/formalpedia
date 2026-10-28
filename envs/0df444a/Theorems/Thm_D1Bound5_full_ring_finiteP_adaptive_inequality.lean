-- Prove2me | Theorems.Thm_D1Bound5_full_ring_finiteP_adaptive_inequality
-- name    : D1Bound5.full_ring_finiteP_adaptive_inequality
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:47:01.50669+00:00
-- url     : https://prove2.me/theorems/f895f25d-e721-4bf5-9b6e-9ff2979900fa
-- title:
--   Full ring finite P adaptive inequality
-- statement:
--   The actual finite P matrix supplies a nonzero integral form on five distinct D(1) entries, with its explicit height and residual bounds. No row-selection or root-lifting premise remains.
-- source:
--   D1Bound5/FinitePAdaptiveFullRing.lean, lines 9-96, SHA-256 30c9805c6cc181642d68a0d16d5bd8f87aa4f1329a6aa8a64967ac56112c9dbe. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_FinitePAdaptiveResidual_Definitions
import Definitions.Def_D1Bound5_IsD1

section
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.full_ring_finiteP_adaptive_inequality
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {S : Finset (𝓞 K)} (hS : IsD1 S) (a : Fin 3 → 𝓞 K) (c d : 𝓞 K)
    (haS : ∀ j, a j ∈ S) (hcS : c ∈ S) (hdS : d ∈ S)
    (hinj : Function.Injective a) (hac : ∀ j, a j ≠ c)
    (had : ∀ j, a j ≠ d) (hcd : c ≠ d)
    (hmon : Monotone (fun j => ‖phi (a j : K)‖))
    (hCT : 200*‖phi (a 2 : K)‖ ≤ ‖phi (c : K)‖)
    (hCD : ‖phi (c : K)‖ ≤ ‖phi (d : K)‖)
    (hAC : 1000 ≤ ‖phi (a 0 : K)‖*‖phi (c : K)‖)
    (q : ℝ) (hq : 1 ≤ q) (hqab : q*‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖) :
    ∃ z : 𝓞 K, z^2 = c*d+1 ∧
      1 < 2400*max (‖phi (a 1 : K)‖*‖phi (a 2 : K)‖^3)
          (‖phi (a 1 : K)‖^3*‖phi (a 2 : K)‖^2)*‖phi (c : K)‖^3/‖phi (z : K)‖+
        finitePAdaptiveRate (1/q)*‖phi (a 2 : K)‖^2*‖phi (z : K)‖/
          (‖phi (a 0 : K)‖^3*‖phi (c : K)‖^5) := by sorry

end D1Bound5
end
