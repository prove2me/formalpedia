-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_negative_jump_generator_distinguishes_ruin_overshoot_from_zero_landing
-- name    : AvramDividend.Classical.avram_wave6_04_actual_negative_jump_generator_distinguishes_ruin_overshoot_from_zero_landing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:51:59.209627+00:00
-- url     : https://prove2.me/theorems/ed065312-2445-4a09-8321-4704926de918
-- title:
--   Original negative-jump generator respects strict ruin overshoot versus exact zero landing
-- statement:
--   For the genuine spectrally negative source generatorIntegrand and a payoff continuous on the nonnegative half-line with zero extension strictly below zero, a downward jump z < -y has value -w(y) minus the exact small-jump derivative correction, whereas the jump z=-y landing exactly at zero retains w(0). The original truncation is (Ioo (-1) 1).indicator 1; no hypothesis wrongly forces w(0)=0.
-- source:
--   Wave6 Chat04 endpoint discontinuity of corrected original Itô–Meyer negative jump generator; unfolded source generatorIntegrand.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_negative_jump_generator_distinguishes_ruin_overshoot_from_zero_landing
    (w : ℝ → ℝ) (y : ℝ) (hy : 0 < y)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0) :
    (∀ z : ℝ, z < -y →
      SpectrallyNegativeLevy.generatorIntegrand w y z =
        -w y - deriv w y * z * (Ioo (-1 : ℝ) 1).indicator 1 z) ∧
    SpectrallyNegativeLevy.generatorIntegrand w y (-y) =
      w 0 - w y - deriv w y * (-y) *
        (Ioo (-1 : ℝ) 1).indicator 1 (-y) := by sorry
