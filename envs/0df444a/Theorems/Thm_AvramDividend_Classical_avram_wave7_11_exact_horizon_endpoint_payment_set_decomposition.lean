-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_exact_horizon_endpoint_payment_set_decomposition
-- name    : AvramDividend.Classical.avram_wave7_11_exact_horizon_endpoint_payment_set_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:06:49.174833+00:00
-- url     : https://prove2.me/theorems/0fe4e483-29b2-4975-9cc8-6e0a6ee5b183
-- title:
--   Exact original Stieltjes payment-set split between strict min-clock and terminal endpoint
-- statement:
--   For a nonnegative finite real horizon T, the canonical original paymentTimes σ ∩ Iic T is exactly the union of the strict paymentTimes of min(σ, ENNReal.ofReal T) and the original payment set's possible contribution at the singleton {T}. This identifies and retains any original dividend atom at the finite endpoint, rather than silently discarding it when replacing the horizon condition by a minimum stopping clock.
-- source:
--   Exact set decomposition from W7-11 payment clock endpoint containment (new independent helper) and min-clock monotonicity; guards canonical UBV finite-horizon payout against loss of the T endpoint atom.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_truncated_clock_only_loses_horizon_endpoint

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_exact_horizon_endpoint_payment_set_decomposition
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes σ ∩ Iic T =
      (paymentTimes (min σ (ENNReal.ofReal T)) ∩ Iic T) ∪
        ((paymentTimes σ ∩ Iic T) ∩ {T}) := by sorry
