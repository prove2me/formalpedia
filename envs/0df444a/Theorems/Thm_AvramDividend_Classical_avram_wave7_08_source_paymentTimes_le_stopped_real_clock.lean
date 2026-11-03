-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_paymentTimes_le_stopped_real_clock
-- name    : AvramDividend.Classical.avram_wave7_08_source_paymentTimes_le_stopped_real_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:25:22.832003+00:00
-- url     : https://prove2.me/theorems/2cceb7f6-66c8-4e3b-ae37-7ba55f804b30
-- title:
--   Original truncated payment times lie before the actual finite real-valued stopped ruin clock
-- statement:
--   The canonical dividend payment epochs under truncated ENNReal clock min(σ,n), including the mandatory zero dividend atom, lie in the original pre-ruin payment domain and at or before the real finite clock obtained by converting min(σ,n) with toNNReal. This is the precise payment-domain inclusion needed to compare the W7-08 cash integral with the stopped source Cash observable in the already-Proved conditional W6-06 Itô budget.
-- source:
--   Derived from Proved original payment support db25d81e and pinned ENNReal.coe_toNNReal / ENNReal.ofReal_lt_coe_iff, preserving the source ℝ≥0∞ first-passage time and the exact Stieltjes payout domain.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_paymentTimes_le_stopped_real_clock
    (σ : ℝ≥0∞) (n : ℕ) (hn : 0 < n) :
    paymentTimes (min σ (n : ℝ≥0∞)) ⊆
      paymentTimes σ ∩ Iic (((min σ (n : ℝ≥0∞)).toNNReal : ℝ≥0) : ℝ) := by sorry
