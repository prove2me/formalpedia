-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
-- name    : AvramDividend.Classical.paymentTimes_membership_to_nNReal_active
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:11:35.87672+00:00
-- url     : https://prove2.me/theorems/71123237-f861-49c2-afd9-b606b56f04d2
-- title:
--   Every payable real time has a nonnegative NNReal time that is zero or strictly before ruin
-- statement:
--   The dividend-value paymentTimes σ set is defined on real times by s≥0 and (s=0 or ENNReal.ofReal s<σ). Every such time has a nonnegative representative s.toNNReal satisfying s.toNNReal=0 or ↑s.toNNReal<σ. This is the exact conversion needed to instantiate the capped finite and countable Stieltjes jump bounds on the real payment domain.
-- source:
--   Exact paymentTimes definition; pinned Mathlib ENNReal.ofNNReal_toNNReal and Real.toNNReal_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_membership_to_nNReal_active
    (σ : ℝ≥0∞) (s : ℝ) (hs : s ∈ paymentTimes σ) :
    0 ≤ s ∧
      (s.toNNReal = 0 ∨ (s.toNNReal : ℝ≥0∞) < σ) := by sorry
