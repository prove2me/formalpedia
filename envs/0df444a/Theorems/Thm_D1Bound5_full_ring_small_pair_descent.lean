-- Prove2me | Theorems.Thm_D1Bound5_full_ring_small_pair_descent
-- name    : D1Bound5.full_ring_small_pair_descent
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:38:19.031207+00:00
-- url     : https://prove2.me/theorems/5d9d0f8b-c35f-4ea0-b1a1-ef169d34075d
-- title:
--   Full ring small pair descent
-- statement:
--   The complete norm-decreasing small-pair mutation in the full ring of integers. All input roots are arbitrary fixed roots; the output is one of the two canonical sign neighbors computed from those same roots. Zero output roots and a zero output extension are permitted.
-- source:
--   D1Bound5/FullRingDescent.lean, lines 9-75, SHA-256 910654eaf77c21677f830c425e228de882932990f2aacb1ab8d02acbad0e4650. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_DescentAlgebra_Definitions

section
open scoped NumberField
open Module

namespace D1Bound5


theorem _root_.D1Bound5.full_ring_small_pair_descent
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a b z r0 r s : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a*b+1 ≠ 0)
    (h0 : r0^2 = a*b+1) (hr : r^2 = a*z+1) (hs : s^2 = b*z+1)
    (hA : ‖phi (a : K)‖ < 3) (hB : ‖phi (b : K)‖ < 3)
    (hZ : 33 ≤ ‖phi (z : K)‖) :
    ∃ w : 𝓞 K,
      (w = mutate a b z r0 r s ∨ w = mutate a b z r0 r (-s)) ∧
      (∃ r' : 𝓞 K, r'^2 = a*w+1) ∧
      (∃ s' : 𝓞 K, s'^2 = b*w+1) ∧
      ‖phi (w : K)‖ < ‖phi (z : K)‖/5+26 ∧
      ‖phi (w : K)‖ < ‖phi (z : K)‖ ∧
      ‖phi (w : K)‖^2 < ‖phi (z : K)‖^2 := by sorry

end D1Bound5
end
