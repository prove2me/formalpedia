-- Prove2me | Theorems.Thm_D1Bound5_full_ring_retained_three_mixed_lower_upper
-- name    : D1Bound5.full_ring_retained_three_mixed_lower_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:31:57.011159+00:00
-- url     : https://prove2.me/theorems/aad391d2-b5c0-4eb5-8a5e-71029befc997
-- title:
--   Full ring retained three mixed lower upper
-- statement:
--   Both manuscript parameter rows for the actual retained three-anchor form with a potentially small first entry. The two successive actual L2 gaps supply the zero-window contradiction and the integral lower bound; no root integrality or nonvanishing premise is assumed.
-- source:
--   D1Bound5/CoherentRetainedMixedForms.lean, lines 31-133, SHA-256 eb96a42cf210b66dfcce899bd150fc1582a3f153a19beef7c93531438f527556. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions
import Definitions.Def_D1Bound5_CoherentPolynomialWeights_Definitions
import Definitions.Def_D1Bound5_CoherentQuotientForms_Definitions
import Definitions.Def_D1Bound5_CoherentRetainedMixedForms_Definitions
import Definitions.Def_D1Bound5_IsD1

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5






theorem _root_.D1Bound5.full_ring_retained_three_mixed_lower_upper
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup)
    (a : Fin 5 → 𝓞 K) (hinj : Function.Injective a) (hmem : ∀ i, a i ∈ Tup)
    (hA : 1 ≤ ‖phi (a 0 : K)‖) (hB : 3 ≤ ‖phi (a 1 : K)‖)
    (hAB : ‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hBS : ‖phi (a 1 : K)‖ ≤ ‖phi (a 2 : K)‖)
    (hfrontier : 2*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖)
    (hproduct : 3*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖ < ‖phi (a 4 : K)‖)
    (H lam U : ℝ) (hrow : CoherentRetainedRow H lam U)
    (hAT : H ≤ ‖phi (a 0 : K)‖*‖phi (a 3 : K)‖)
    (eta : ℂ) (heta : eta^2 = phi (a 3 : K)*phi (a 4 : K)) :
    let v : Fin 3 → ℂ := fun i => phi (a (![0,1,2] i) : K)
    let L := coherentQuotientForm v (coherentVandermonde3 v)
      (phi (a 3 : K)) (phi (a 4 : K)) eta
    let Z := ‖coherentTerminalRoot (phi (a 3 : K)) (phi (a 4 : K)) eta‖
    ‖phi (a 1 : K)‖^2*‖phi (a 3 : K)‖^3 < (10001/10000 : ℝ)*‖phi (a 4 : K)‖ ∧
      L ≠ 0 ∧ 1 ≤ ‖L‖ ∧
      ‖L‖ < 51*‖coherentVandermonde3 v‖/(100*Z) +
        lam*‖coherentVandermonde3 v‖*Z/
          (‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖^3) := by sorry

end D1Bound5
end
