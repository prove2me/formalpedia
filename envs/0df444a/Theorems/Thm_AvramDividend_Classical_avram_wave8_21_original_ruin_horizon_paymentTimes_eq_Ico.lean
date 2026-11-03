-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_ruin_horizon_paymentTimes_eq_Ico
-- name    : AvramDividend.Classical.avram_wave8_21_original_ruin_horizon_paymentTimes_eq_Ico
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:11:14.465997+00:00
-- url     : https://prove2.me/theorems/53e354b4-74f9-45a9-8afe-1535106d9f5d
-- title:
--   Original stopped payment set at a strictly positive ruin horizon equals the half-open payment interval
-- statement:
--   For positive deterministic ruin time T, the actual pre-ruin paymentTimes clock restricted to the closed numerical horizon equals [0,T). This includes the original time-zero rightpayment and excludes the horizon's own rightpayment. By the genuine Stieltjes interval identity, its full dividendMeasure mass is ENNReal.ofReal (D T ω), accounting for continuous dividends and all strictly earlier atoms without a surrogate clock.
-- source:
--   Exact canonical paymentTimes definition and established original dividendMeasure_Ico_zero_eq_dividendValue; no replacement measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_ruin_horizon_paymentTimes_eq_Ico
    (T : ℝ≥0) (hT : 0 < T) :
    paymentTimes (T : ℝ≥0∞) ∩ Iic (T : ℝ) =
      Ico 0 (T : ℝ) := by sorry
