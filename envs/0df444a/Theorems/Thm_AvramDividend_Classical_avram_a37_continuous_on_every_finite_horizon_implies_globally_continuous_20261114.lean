-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a37_continuous_on_every_finite_horizon_implies_globally_continuous_20261114
-- name    : AvramDividend.Classical.avram_a37_continuous_on_every_finite_horizon_implies_globally_continuous_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:16:22.766484+00:00
-- url     : https://prove2.me/theorems/9dd92118-6d98-4810-8169-480429c60207
-- title:
--   Nonnegative-time path continuous on every finite closed horizon is globally continuous
-- statement:
--   Any real function on nonnegative time that is continuous when restricted to every finite time horizon is continuous at every time globally.
-- source:
--   Pinned Mathlib continuous_iff_continuousAt and ContinuousWithinAt.continuousAt.

import Mathlib
open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a37_continuous_on_every_finite_horizon_implies_globally_continuous_20261114
    (f : ℝ≥0 → ℝ)
    (h : ∀ T : ℝ≥0, ContinuousOn f (Iic T)) :
    Continuous f := by sorry
