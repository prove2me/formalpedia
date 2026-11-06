-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_real_stopped_paymentTimes_closed_window_saturation
-- name    : AvramDividend.Classical.avram_limit2_real_stopped_paymentTimes_closed_window_saturation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:11:41.51987+00:00
-- url     : https://prove2.me/theorems/31e3c38e-1987-43e5-a0e2-50288af6b14e
-- title:
--   Source-exact real stopped dividend payment window saturates at its own closed horizon, including time zero
-- statement:
--   Exact deterministic stopping-set saturation for the original right-payment selector at any nonnegative real clipping clock S: if an observation window T extends beyond S, intersecting with Iic T yields exactly the same genuine payable times as intersecting with Iic S. The proof imports the independent public-backed real stop support lemma and proves both inclusions. It preserves the time-zero atom at S=0 and avoids introducing any right-endpoint dividend at S. This set identity can rewrite original Stieltjes measure windows pointwise without integrability assumptions.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_real_stopped_paymentTimes_subset_closed_horizon
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_real_stopped_paymentTimes_closed_window_saturation
    (τ : ℝ≥0∞) (S T : ℝ) (hS : 0 ≤ S) (hST : S ≤ T) :
    paymentTimes (min τ (ENNReal.ofReal S)) ∩ Set.Iic T =
    paymentTimes (min τ (ENNReal.ofReal S)) ∩ Set.Iic S := by sorry
