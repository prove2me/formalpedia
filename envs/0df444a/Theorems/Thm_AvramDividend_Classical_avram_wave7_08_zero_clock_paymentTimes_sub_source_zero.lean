-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_zero_clock_paymentTimes_sub_source_zero
-- name    : AvramDividend.Classical.avram_wave7_08_zero_clock_paymentTimes_sub_source_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:53:29.375203+00:00
-- url     : https://prove2.me/theorems/91cebf31-749b-4fa0-8ed7-ca3f2f8533c2
-- title:
--   At zero stopped horizon original payment times lie in source time-zero payout atom
-- statement:
--   For any source ruin horizon and any real observation horizon, every dividend payment time admissible under the zero-truncated clock lies at t=0 and hence lies in the original source paymentTimes intersected with Iic 0. This preserves the initial dividend atom and is the n=0 branch needed for uniform truncated HJB budgets.
-- source:
--   Uses the exact canonical paymentTimes definition; no positive n assumption and no change to the source dividend measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_zero_clock_paymentTimes_sub_source_zero
    (σ : ℝ≥0∞) (T : ℝ) :
    paymentTimes (min σ (0 : ℝ≥0∞)) ∩ Iic T ⊆
      paymentTimes σ ∩ Iic (0 : ℝ) := by sorry
