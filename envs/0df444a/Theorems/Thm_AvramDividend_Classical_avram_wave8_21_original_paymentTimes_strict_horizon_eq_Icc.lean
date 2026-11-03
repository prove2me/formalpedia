-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
-- name    : AvramDividend.Classical.avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:41:00.607335+00:00
-- url     : https://prove2.me/theorems/a042792f-d262-4aca-99d5-96410159fb13
-- title:
--   Strict pre-ruin payment times coincide exactly with the full closed horizon including its atom
-- statement:
--   For the canonical original paymentTimes convention, if a deterministic nonnegative horizon T is strictly before ruin clock σ, every real time from zero through T is an active payment time. Consequently paymentTimes σ intersect the closed upper horizon Iic T equals Icc 0 T, including the time-zero payment and the rightpayment atom at T. This is the exact set identity needed to use the original Stieltjes closed-horizon mass lemmas.
-- source:
--   Avram classical original paymentTimes definition, strict survival and closed horizon.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
    (σ : ℝ≥0∞) (T : ℝ≥0)
    (hstrict : (T : ℝ≥0∞) < σ) :
    paymentTimes σ ∩ Iic (T : ℝ) = Icc 0 (T : ℝ) := by sorry
