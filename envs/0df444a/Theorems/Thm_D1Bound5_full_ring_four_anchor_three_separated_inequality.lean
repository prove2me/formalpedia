-- Prove2me | Theorems.Thm_D1Bound5_full_ring_four_anchor_three_separated_inequality
-- name    : D1Bound5.full_ring_four_anchor_three_separated_inequality
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:34:20.428498+00:00
-- url     : https://prove2.me/theorems/9e6b82fa-7f97-4b95-9790-cee8a7a3d719
-- title:
--   Full ring four anchor three separated inequality
-- statement:
--   Four actual anchors select a nonzero integral three-anchor form. Both alternatives use the same analytic terminal root, and the smaller third anchor is bounded by the fourth.
-- source:
--   D1Bound5/FullRingThreeSelection.lean, lines 52-111, SHA-256 2e2cbb4843f28a0f2078cbc079307336d3600266b5a7fc9be4978928cce50c2d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_IsD1

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.full_ring_four_anchor_three_separated_inequality
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {Tup : Finset (𝓞 K)} (hTup : IsD1 Tup) {p q : 𝓞 K}
    (hp : p ∈ Tup) (hq : q ∈ Tup) (hpq : p ≠ q)
    (a : Fin 4 → 𝓞 K) (hinj : Function.Injective a)
    (ha : ∀ i, a i ∈ Tup) (hap : ∀ i, a i ≠ p) (haq : ∀ i, a i ≠ q)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hP : 1000 ≤ ‖phi (p : K)‖)
    (hTP : 4*‖phi (a 3 : K)‖ ≤ ‖phi (p : K)‖)
    (hQ : 4*‖phi (p : K)‖ ≤ ‖phi (q : K)‖)
    (hsize : 32*‖phi (a 1 : K)‖*‖phi (a 2 : K)‖*‖phi (a 3 : K)‖/
      ‖phi (a 0 : K)‖^3 ≤ ‖phi (p : K)‖^2)
    (eta : ℂ) (heta : eta^2 = phi (p : K)*phi (q : K)) :
    1 < 5*‖phi (a 1 : K)‖*‖phi (a 3 : K)‖^2/
          ‖coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta‖ +
      3*‖phi (a 3 : K)‖*‖coherentTerminalRoot (phi (p : K)) (phi (q : K)) eta‖/
        (4*‖phi (a 0 : K)‖*‖phi (p : K)‖^3) := by sorry

end D1Bound5
end
