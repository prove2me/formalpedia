-- Prove2me | Theorems.Thm_D1Bound5_full_ring_retained_three_h48_lower_upper
-- name    : D1Bound5.full_ring_retained_three_h48_lower_upper
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:18:18.793616+00:00
-- url     : https://prove2.me/theorems/e8e9272a-86c7-42ce-8e20-74274da7208e
-- title:
--   Full ring retained three h48 lower upper
-- statement:
--   The actual retained three-anchor form has both its integral lower bound and the H48 analytic upper bound in the no-small-entry branch. The nonzero-form premise is discharged using the actual strong L2 gap; no chosen-root integrality or tail estimate is assumed.
-- source:
--   D1Bound5/CoherentRetainedIntegral.lean, lines 55-141, SHA-256 8fac0734c7218c5f7863cf6315d86f4eee91becdf95c83fd3622b76ed6b54058. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_IsD1

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.full_ring_retained_three_h48_lower_upper
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup)
    (a : Fin 5 → 𝓞 K) (hinj : Function.Injective a) (hmem : ∀ i, a i ∈ Tup)
    (hA : 3 ≤ ‖phi (a 0 : K)‖)
    (hAB : ‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hBS : ‖phi (a 1 : K)‖ ≤ ‖phi (a 2 : K)‖)
    (hfrontier : 2*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖ < ‖phi (a 3 : K)‖)
    (hproduct : 3*‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖ < ‖phi (a 4 : K)‖)
    (eta : ℂ) (heta : eta^2 = phi (a 3 : K)*phi (a 4 : K)) :
    let v : Fin 3 → ℂ := fun i => phi (a (![0,1,2] i) : K)
    let L := coherentQuotientForm v (coherentVandermonde3 v)
      (phi (a 3 : K)) (phi (a 4 : K)) eta
    let Z := ‖coherentTerminalRoot (phi (a 3 : K)) (phi (a 4 : K)) eta‖
    L ≠ 0 ∧ 1 ≤ ‖L‖ ∧
      ‖L‖ < 51*‖coherentVandermonde3 v‖/(100*Z) +
        (19/200 : ℝ)*‖coherentVandermonde3 v‖*Z/
          (‖phi (a 0 : K)‖*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖^3) := by sorry

end D1Bound5
end
