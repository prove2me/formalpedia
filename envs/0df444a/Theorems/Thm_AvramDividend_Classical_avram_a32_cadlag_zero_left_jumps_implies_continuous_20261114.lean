-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a32_cadlag_zero_left_jumps_implies_continuous_20261114
-- name    : AvramDividend.Classical.avram_a32_cadlag_zero_left_jumps_implies_continuous_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:59:24.006796+00:00
-- url     : https://prove2.me/theorems/35fbc728-19d3-4d9e-9f3a-67262d0f4a61
-- title:
--   Right-continuous path with matching left limits is continuous
-- statement:
--   A right-continuous real path on nonnegative time is continuous everywhere if its left limit equals its present value at every strictly positive time.
-- source:
--   Mathlib left and right continuity criterion.

import Mathlib
open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a32_cadlag_zero_left_jumps_implies_continuous_20261114
    (f : ℝ≥0 → ℝ)
    (hRight : ∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t : ℝ≥0, 0 < t →
      Tendsto f (𝓝[<] t) (𝓝 (f t))) :
    ∀ t : ℝ≥0, ContinuousAt f t := by sorry
