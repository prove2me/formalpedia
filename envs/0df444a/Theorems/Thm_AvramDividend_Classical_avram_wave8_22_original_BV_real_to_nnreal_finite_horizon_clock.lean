-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_real_to_nnreal_finite_horizon_clock
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_real_to_nnreal_finite_horizon_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:18:17.459198+00:00
-- url     : https://prove2.me/theorems/be5c6353-51ba-4861-a868-d71d09c221e2
-- title:
--   Finite mass of exact original BV deterministic stopped real-to-NNReal time clock
-- statement:
--   The original deterministic μT clock is precisely the Real.toNNReal pushforward of Lebesgue measure restricted to the finite interval [0,T]. This original clock has finite total mass for every finite NNReal T, discharging hμfinite in finite-clock expected generator estimates.
-- source:
--   Pinned Mathlib Real.isFiniteMeasure_restrict_Icc and Measure.isFiniteMeasure_map; exact original source hTime.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_real_to_nnreal_finite_horizon_clock (T : ℝ≥0) (μT : Measure ℝ≥0)
  (hTime : μT = (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) :
  μT Set.univ < ∞ := by sorry
