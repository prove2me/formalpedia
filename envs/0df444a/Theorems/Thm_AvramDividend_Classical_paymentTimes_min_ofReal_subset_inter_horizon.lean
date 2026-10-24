-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_subset_inter_horizon
-- name    : AvramDividend.Classical.paymentTimes_min_ofReal_subset_inter_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:28:16.270054+00:00
-- url     : https://prove2.me/theorems/153734f3-93a8-471e-b127-37208aaf3970
-- title:
--   Truncated ruin payment times remain before ruin and the finite horizon, including time zero
-- statement:
--   Truncating the ruin clock at any nonnegative real time produces payment times contained in the original strict pre-ruin set intersected with the closed horizon. The proof handles the time-zero dividend atom and zero horizon. This set inclusion is the bridge from canonical min(ruin,n) natural-horizon payoffs to the true finite-horizon capped verification bound.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_min_ofReal_subset_inter_horizon
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes (min σ (ENNReal.ofReal T)) ⊆
      paymentTimes σ ∩ Set.Iic T := by sorry
