-- Prove2me | solution 1 for e7_interval_integral_clamp_toNNReal
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-08T07:04:08.439358+00:00
-- url     : https://prove2.me/submissions/4ed56aae-d8c0-4ea9-930f-be55d63bba48

import Mathlib

open MeasureTheory
open scoped NNReal

theorem solution (q : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, q s.toNNReal) = ∫ s in (0 : ℝ)..t, q s := by
  apply intervalIntegral.integral_congr
  intro x hx
  have hx0 : 0 ≤ x := by
    rw [Set.uIcc_of_le ht] at hx
    exact hx.1
  show q ↑x.toNNReal = q x
  rw [Real.coe_toNNReal x hx0]
