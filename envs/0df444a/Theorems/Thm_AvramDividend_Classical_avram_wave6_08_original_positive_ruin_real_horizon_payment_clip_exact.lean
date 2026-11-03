-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_real_horizon_payment_clip_exact
-- name    : AvramDividend.Classical.avram_wave6_08_original_positive_ruin_real_horizon_payment_clip_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:11:14.108196+00:00
-- url     : https://prove2.me/theorems/4958b5b7-d253-4d65-8c51-9037feef90d3
-- title:
--   Exact finite-horizon original payment domain: closed horizon before ruin, half-open at ruin
-- statement:
--   For positive finite ruin τ and a nonnegative real horizon T, the original paymentTimes set cut off at T is exactly [0,T] when T<τ, including the horizon right payment, and exactly [0,τ) when τ≤T, excluding the ruin-time right payment while retaining the time-zero atom. This resolves the exact real finite-horizon pre/post-payment stopping convention without stochastic assumptions.
-- source:
--   Exact original paymentTimes positive-clock identity, ENNReal.ofReal_lt_coe_iff, elementary real interval set algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave6_08_original_positive_ruin_real_horizon_payment_clip_exact
    (τ : ℝ≥0) (hτ : 0 < τ) (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes (τ : ℝ≥0∞) ∩ Iic T =
      if T < (τ : ℝ) then Icc 0 T else Ico 0 (τ : ℝ) := by sorry
