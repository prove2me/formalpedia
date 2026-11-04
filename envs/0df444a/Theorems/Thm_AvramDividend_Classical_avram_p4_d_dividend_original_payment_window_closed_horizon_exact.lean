-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_payment_window_closed_horizon_exact
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_payment_window_closed_horizon_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:31:52.217033+00:00
-- url     : https://prove2.me/theorems/0ecad334-0c98-4852-b6a9-cf35beaf7f21
-- title:
--   Literal original payable time window equals nonnegative closed horizon including time zero
-- statement:
--   The original paymentTimes definition always selects nonnegative real times, including the distinguished time zero and excluding positive ruin-time right payments. The exact Proved paymentTimes_membership_to_nNReal_active theorem transports this nonnegativity to identify the literal P4-F paymentTimes(ruinTime)∩Iic T with paymentTimes(ruinTime)∩Icc 0 T for every finite stopped horizon T, including T=0. This bridges closed-interval original Stieltjes atom/diffuse lemmas to the canonical stopped cash selector without a survival assumption.
-- source:
--   Original admissibility/paymentTimes definitions; Proved 71123237-f861-49c2-afd9-b606b56f04d2 and P4-F 0dda1be7 exact payment domain

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_payment_window_closed_horizon_exact
    (σ : ℝ≥0∞) (T : ℝ≥0) :
    paymentTimes σ ∩ Iic (T : ℝ) =
      paymentTimes σ ∩ Icc (0 : ℝ) (T : ℝ) := by sorry
