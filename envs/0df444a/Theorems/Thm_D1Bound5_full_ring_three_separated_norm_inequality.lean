-- Prove2me | Theorems.Thm_D1Bound5_full_ring_three_separated_norm_inequality
-- name    : D1Bound5.full_ring_three_separated_norm_inequality
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:08:21.741159+00:00
-- url     : https://prove2.me/theorems/cb906ae2-e375-4743-bc6e-a0a52bfa4ee7
-- title:
--   Full ring three separated norm inequality
-- statement:
--   The separated three-anchor inequality for actual integral entries. Only the vanishing decision is left to a subsequent four-anchor lemma.
-- source:
--   D1Bound5/FullRingThreeSelection.lean, lines 9-50, SHA-256 2e2cbb4843f28a0f2078cbc079307336d3600266b5a7fc9be4978928cce50c2d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Tactic.ComputeDegree
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


theorem _root_.D1Bound5.full_ring_three_separated_norm_inequality
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup) {p q : 𝓞 K}
    (hp : p ∈ Tup) (hq : q ∈ Tup) (hpq : p ≠ q)
    (a : Fin 3 → 𝓞 K) (hinj : Function.Injective a)
    (ha : ∀ i, a i ∈ Tup) (hap : ∀ i, a i ≠ p) (haq : ∀ i, a i ≠ q)
    (hAB : ‖phi (a 0 : K)‖ ≤ ‖phi (a 1 : K)‖)
    (hBS : ‖phi (a 1 : K)‖ ≤ ‖phi (a 2 : K)‖)
    (hP : 0 < ‖phi (p : K)‖) (hAP : 1000 ≤ ‖phi (a 0 : K)‖*‖phi (p : K)‖)
    (hQ : 4*‖phi (p : K)‖ ≤ ‖phi (q : K)‖)
    (hPQ : 10000 < ‖phi (p : K)‖*‖phi (q : K)‖)
    (eta : ℂ) (heta : eta^2 = phi (p : K)*phi (q : K))
    (hL : coherentQuotientForm (fun i => phi (a i : K))
      (coherentVandermonde3 (fun i => phi (a i : K)))
        (phi (p : K)) (phi (q : K)) eta ≠ 0) :
    1 < 5*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖^2/
          ‖coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta‖ +
      3*‖phi (a 2 : K)‖*‖coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta‖/
        (4*‖phi (a 0 : K)‖*‖phi (p : K)‖^3) := by sorry



end D1Bound5
end
