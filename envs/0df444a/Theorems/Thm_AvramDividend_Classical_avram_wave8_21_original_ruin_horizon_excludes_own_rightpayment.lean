-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_ruin_horizon_excludes_own_rightpayment
-- name    : AvramDividend.Classical.avram_wave8_21_original_ruin_horizon_excludes_own_rightpayment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:41:18.202236+00:00
-- url     : https://prove2.me/theorems/cfece5b3-ebbb-47cf-8a4b-dbbc5ffa7c1f
-- title:
--   Actual original payment clock includes time zero and excludes a positive ruin horizon atom
-- statement:
--   For the canonical original paymentTimes convention, zero remains a candidate right-payment time even when the ruin clock is a finite positive horizon T, whereas a right-payment at T is excluded because its definition demands strict pre-ruin time. This gives W8-04 the complementary endpoint convention to the strict-survival Icc identity, without changing the Stieltjes dividend measure.
-- source:
--   Original classical dividend strategy paymentTimes, exact equal-to-ruin endpoint, no surrogate measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_ruin_horizon_excludes_own_rightpayment
    (T : ℝ≥0) (hT : 0 < T) :
    (0 : ℝ) ∈ paymentTimes (T : ℝ≥0∞) ∧
    ((T : ℝ) ∉ paymentTimes (T : ℝ≥0∞)) := by sorry
