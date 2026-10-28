-- Prove2me | Theorems.Thm_D1Bound5_full_ring_one_three_negative_extension
-- name    : D1Bound5.full_ring_one_three_negative_extension
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:22:06.31979+00:00
-- url     : https://prove2.me/theorems/77db38fe-7ea8-47e7-b6a7-b6653300ba4a
-- title:
--   Full ring one three negative extension
-- statement:
--   Among extensions of 1 and 3, a negative one forces all other nonzero compatible entries to be negative odd rational integers.
-- source:
--   D1Bound5/OneThreeNegative.lean, lines 126-158, SHA-256 608590903d9651b83081c7c7b14962c497bd29944ae7411568eb23eee5734f08. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

section
open scoped NumberField
open Module

namespace D1Bound5























theorem _root_.D1Bound5.full_ring_one_three_negative_extension
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) {n : ℤ} (hn : n < 0)
    (hnr : ∃ r : 𝓞 K, r*r = (n : 𝓞 K)+1)
    (hns : ∃ s : 𝓞 K, s*s = 3*(n : 𝓞 K)+1)
    {z : 𝓞 K} (hz : z ≠ 0)
    (hzr : ∃ r : 𝓞 K, r*r = z+1)
    (hzs : ∃ s : 𝓞 K, s*s = 3*z+1)
    (hzn : z = (n : 𝓞 K) ∨ ∃ r : 𝓞 K, r*r = z*(n : 𝓞 K)+1) :
    ∃ p : ℤ, z=(p : 𝓞 K) ∧ p<0 ∧ p%2=1 := by sorry








end D1Bound5
end
