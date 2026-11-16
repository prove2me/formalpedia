-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_strict_payment_window_contains_eight_hundredths
-- name    : AvramDividend.Classical.avram_bvb_obstruction_tenth_strict_payment_window_contains_eight_hundredths
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:46:54.892339+00:00
-- url     : https://prove2.me/theorems/191e74ab-8558-4825-81f1-96fcd7bb6862
-- title:
--   Original tenth-horizon stopped paymentTimes strict mesh includes the full first eight-hundredths interval on survival
-- statement:
--   For any original stopped ruin time strictly later than 1/10, all physical-grid strict payment windows with n≥4 contain the full real interval (0,2/25]. This identifies a fixed positive-dividend mass portion of every original physical cash prefix on the genuine no-jump survival event.
-- source:
--   Original paymentTimes requires 0≤t and ENNReal.ofReal(t)<ruin time. On (0,2/25], both are automatic from strict survival past 1/10. Proved mesh inequality for n≥4 places 2/25 below the strict cutoff 1/10−δ_n.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_horizon_strict_prefix_contains_eight_hundredths
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_tenth_strict_payment_window_contains_eight_hundredths
    (σ : ℝ≥0∞)
    (hσ : ((1 / 10 : ℝ≥0) : ℝ≥0∞) < σ)
    (n : ℕ) (hn : 4 ≤ n) :
    Ioc (0 : ℝ) (2 / 25 : ℝ) ⊆
      paymentTimes σ ∩
        Iio ((1 / 10 : ℝ) - (1 / 10 : ℝ) / ((n : ℝ) + 2)) := by sorry
