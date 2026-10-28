-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_iInter_diff_iInf_subset_terminal
-- name    : AvramDividend.Classical.paymentTimes_iInter_diff_iInf_subset_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:42:54.449975+00:00
-- url     : https://prove2.me/theorems/70dd30b6-6d24-486a-9c5f-4c338fdc4373
-- title:
--   Only the terminal time can survive all shrinking pre-ruin payment windows
-- statement:
--   For any sequence of extended nonnegative stopping horizons, a payment time that lies strictly before every horizon but fails the strict payment-time condition at their infimum must coincide with the limiting horizon. The distinguished time-zero payment remains included. Combined with the previously proved absence of running-supremum Stieltjes atoms, this controls the only endpoint discrepancy when taking a countable zero-barrier limit.
-- source:
--   Exact published paymentTimes definition; needed with Proved runningSup_dividendMeasure_no_nonnegative_atoms and barrierRuinTime_zero_eq_iInf_reciprocal for zero-cap boundary evaluation.

import Definitions.Def_AvramDividend_Classical_DividendStrategy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.paymentTimes_iInter_diff_iInf_subset_terminal
    (σ : ℕ → ℝ≥0∞) :
    (⋂ n, paymentTimes (σ n)) \
        paymentTimes (⨅ n, σ n) ⊆
      {t : ℝ | ENNReal.ofReal t = ⨅ n, σ n} := by sorry
