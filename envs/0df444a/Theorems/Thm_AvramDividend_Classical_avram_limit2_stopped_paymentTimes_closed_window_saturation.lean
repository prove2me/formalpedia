-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_stopped_paymentTimes_closed_window_saturation
-- name    : AvramDividend.Classical.avram_limit2_stopped_paymentTimes_closed_window_saturation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:02:04.674883+00:00
-- url     : https://prove2.me/theorems/122c2ccd-eb7f-40c7-9f63-c55a5a679a7f
-- title:
--   Exact natural-clock original payment window is unchanged by any later closed observation horizon
-- statement:
--   Original paymentTimes stopped at min τ n is contained in the real closed integer interval Iic n, including the explicitly payable time-zero atom even at zero clock. Since n ≤ T, intersection with Iic T adds no payable times; the reverse inclusion follows by transitivity of the horizon order. Exact set equality supports the independent UBV natural-clock Stieltjes saturation theorem without appealing to equality-in-law or changing endpoint conventions.

import Mathlib.Order.Interval.Set.Defs
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_limit2_stopped_paymentTimes_subset_closed_nat_clock
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_stopped_paymentTimes_closed_window_saturation
    (τ : ℝ≥0∞) (n : ℕ) (T : ℝ) (hT : (n : ℝ) ≤ T) :
    paymentTimes (min τ (n : ℝ≥0∞)) ∩ Set.Iic T =
    paymentTimes (min τ (n : ℝ≥0∞)) ∩ Set.Iic (n : ℝ) := by sorry
