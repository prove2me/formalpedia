-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_large_negative_ruin_overshoot_generator_no_small_mark_compensation
-- name    : AvramDividend.Classical.avram_wave6_04_actual_large_negative_ruin_overshoot_generator_no_small_mark_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:02:10.191659+00:00
-- url     : https://prove2.me/theorems/0e7e9113-18e9-472c-bf68-b45554065932
-- title:
--   Original large-negative ruin overshoot generator is uncompensated and equals minus the reserve payoff
-- statement:
--   For the original SpectrallyNegativeLevy.generatorIntegrand with a payoff equal to zero strictly below zero, a jump z≤-1 crossing the prepayment reserve below ruin has no small-mark derivative compensation, and its exact nonlinear generator integrand is -w(y). This explicitly handles large negative Lévy marks, including the correct strict inequality at ruin.
-- source:
--   Wave6 Chat04 genuine original source truncation and negative-extension large-jump terminal branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_actual_large_negative_ruin_overshoot_generator_no_small_mark_compensation
    (w : ℝ → ℝ) (y z : ℝ)
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hy : 0 < y) (hz_large : z ≤ -1) (hover : y + z < 0) :
    SpectrallyNegativeLevy.generatorIntegrand w y z = -w y := by sorry
