-- Prove2me | Theorems.Thm_D1Bound5_full_ring_coherent_two_strong_gap_main
-- name    : D1Bound5.full_ring_coherent_two_strong_gap_main
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:18:20.902979+00:00
-- url     : https://prove2.me/theorems/90190b21-27cc-4f29-bbdb-1c504d97bc7d
-- title:
--   Full ring coherent two strong gap main
-- statement:
--   A branch-witness-free strong gap for actual tuple entries in the two main size regimes. All analytic size premises and the auxiliary square root are supplied internally.
-- source:
--   D1Bound5/CoherentTwoMainGap.lean, lines 45-69, SHA-256 c0509ec02d08b12069253aa8808767ae8f26ee3893a3c5b4a0de91ed1e4a0cfd. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_IsD1

section
open Finset
open scoped NumberField
open Module

namespace D1Bound5




theorem _root_.D1Bound5.full_ring_coherent_two_strong_gap_main
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {T : Finset (𝓞 K)} (hT : IsD1 T) {a b p q : 𝓞 K}
    (ha : a ∈ T) (hb : b ∈ T) (hp : p ∈ T) (hq : q ∈ T)
    (hab : a ≠ b) (hap : a ≠ p) (haq : a ≠ q)
    (hbp : b ≠ p) (hbq : b ≠ q) (hpq : p ≠ q)
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖)
    (hB : 3 ≤ ‖phi (b : K)‖) (hP : 5 * ‖phi (b : K)‖ ≤ ‖phi (p : K)‖)
    (hQ : 5 * ‖phi (a : K)‖ * ‖phi (b : K)‖ * ‖phi (p : K)‖ ≤ ‖phi (q : K)‖)
    (hlarge : 3 ≤ ‖phi (a : K)‖ ∨ 48 ≤ ‖phi (p : K)‖) :
    ‖phi (a : K)‖ ^ 2 * ‖phi (p : K)‖ ^ 3 <
      (10001 / 10000 : ℝ) * ‖phi (q : K)‖ := by sorry

end D1Bound5
end
