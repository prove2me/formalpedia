-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_first_up_clock_positive_probability_all_smaller_levels
-- name    : AvramDividend.Classical.unbounded_first_up_clock_positive_probability_all_smaller_levels
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:25:40.4124+00:00
-- url     : https://prove2.me/theorems/7da6d680-de75-49ab-94d4-3a5d52e870be
-- title:
--   Every smaller positive barrier inherits a positive-probability strict upcrossing
-- statement:
--   For an unbounded-variation spectrally negative Lévy process and any positive horizon, there exists a positive level a such that every positive smaller level b ≤ a is crossed strictly before the horizon with positive probability. This strengthens one-witness upcrossing by applying pathwise threshold monotonicity and probability monotonicity.
-- source:
--   Existing proved pre-horizon upcrossing probability and monotonicity of the strict upper exit time in its threshold.

import Theorems.Thm_AvramDividend_Classical_unbounded_first_up_clock_positive_probability_before_horizon
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
import Mathlib.MeasureTheory.OuterMeasure.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_first_up_clock_positive_probability_all_smaller_levels
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ a : ℝ, 0 < a ∧ ∀ b : ℝ, 0 < b → b ≤ a →
      0 < P {ω : Ω | twoSidedExitUpTime X b ω < (t : ℝ≥0∞)} := by sorry
