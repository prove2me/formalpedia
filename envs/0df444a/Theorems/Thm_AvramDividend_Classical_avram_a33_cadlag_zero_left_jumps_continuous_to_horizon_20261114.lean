-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a33_cadlag_zero_left_jumps_continuous_to_horizon_20261114
-- name    : AvramDividend.Classical.avram_a33_cadlag_zero_left_jumps_continuous_to_horizon_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:02:22.568833+00:00
-- url     : https://prove2.me/theorems/7188a5fa-fc9d-4d9a-bdc1-470b428fd365
-- title:
--   Cadlag real paths with no left jumps through a finite horizon are continuous at each time through that horizon
-- statement:
--   A right-continuous real path whose left limit equals its value at every positive time not exceeding a given horizon is continuous at every time up to that horizon.
-- source:
--   Mathlib left/right continuity criterion, bounded-horizon form.

import Mathlib
open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a33_cadlag_zero_left_jumps_continuous_to_horizon_20261114
    (f : ℝ≥0 → ℝ) (T : ℝ≥0)
    (hRight : ∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t : ℝ≥0, 0 < t →
      t ≤ T → Tendsto f (𝓝[<] t) (𝓝 (f t))) :
    ∀ t : ℝ≥0, t ≤ T → ContinuousAt f t := by sorry
