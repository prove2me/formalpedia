-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger101_original_strict_clipped_clock_payment_support
-- name    : AvramDividend.Classical.avram_gledger101_original_strict_clipped_clock_payment_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:40:15.285967+00:00
-- url     : https://prove2.me/theorems/b6a701ac-ec25-459d-9884-db11e6d980da
-- title:
--   A strictly pre-clipped-clock positive time is an original pre-ruin payment time
-- statement:
--   If an NNReal clock is no later than ruin, every strictly positive time before that clock lies in the original strict payment-times set, and is strictly below the clock itself. This supports the real strict dividend-mass to discounted-cash comparison under the genuine clipped-clock hypothesis.
-- source:
--   Ruin-clipped support bridge needed to use gledger100 in the original Gaussian stopped mesh L1 estimate gledger39.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger101_original_strict_clipped_clock_payment_support
    (σ : ℝ≥0∞) (ρ : ℝ≥0) (hρ : (ρ : ℝ≥0∞) ≤ σ) :
    Ioo (0 : ℝ) (ρ : ℝ) ⊆ paymentTimes σ ∩ Iio (ρ : ℝ) := by sorry
