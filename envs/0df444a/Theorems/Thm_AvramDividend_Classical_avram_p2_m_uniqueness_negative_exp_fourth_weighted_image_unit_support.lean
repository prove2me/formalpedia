-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_negative_exp_fourth_weighted_image_unit_support
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_negative_exp_fourth_weighted_image_unit_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:05:47.035699+00:00
-- url     : https://prove2.me/theorems/620b3527-43c1-45fd-aaa2-b04f2e29a843
-- title:
--   A genuine negative-mark fourth-weighted exponential image is supported on the unit interval
-- statement:
--   For any Borel source measure σ concentrated on strictly negative real marks, its fourth-weighted exponential pushforward is concentrated on [0,1], without a finite-measure, stationarity or count-intensity assumption. This discharges the hunit_ρ premise in P2-M's original candidate-source inversion bridge once P2-B proves ρ is the genuine weighted image of its negative candidate source.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_negative_exp_fourth_weighted_image_unit_support
    (σ : Measure ℝ) (hnegσ : ∀ᵐ y ∂σ, y < 0) :
    ∀ᵐ z ∂((σ.withDensity
      (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp),
      z ∈ Icc (0 : ℝ) 1 := by sorry
