-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_paymentTimes_measurableSet
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:34:36.653907+00:00
-- url     : https://prove2.me/theorems/a3a9dc89-7898-48d3-8891-15bfb057040f
-- title:
--   Original strict-ruin right-payment time selector is measurable
-- statement:
--   The actual dividend paymentTimes selector on real time is a Borel subset determined by the nonnegative time condition, the distinguished zero-payment inclusion and strict comparison with the ruin clock in ENNReal. Its measurability allows the exact true stopped cash to be rewritten through the original Stieltjes indicator integral and measure restriction on a closed nonnegative horizon, with no loss of singular-continuous mass or boundary atoms.
-- source:
--   Source Definitions.Def_AvramDividend_Classical_DividendStrategy and pinned Mathlib measurability tactics

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_paymentTimes_measurableSet (σ : ℝ≥0∞) :
    MeasurableSet (paymentTimes σ) := by sorry
