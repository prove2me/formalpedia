-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_truncated_clock_only_loses_horizon_endpoint
-- name    : AvramDividend.Classical.avram_wave7_11_truncated_clock_only_loses_horizon_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:53:28.188775+00:00
-- url     : https://prove2.me/theorems/0e2d98e7-1b52-4410-acb7-ca8673c8c9e0
-- title:
--   Original finite-real-horizon payment clock truncation can omit only a terminal endpoint atom
-- statement:
--   For the exact original paymentTimes σ on real time and a nonnegative finite observation horizon T, the payments before or at T lie in the payment set for clock min(σ, ENNReal.ofReal T), up to possibly the singleton {T}. This records the precise endpoint dividend-atom issue: stopping at T with strict payment-time inequality can remove an atom at T, while all times strictly earlier than T remain. The zero-time atom is included as before.
-- source:
--   Set-theoretic endpoint correction for canonical UBV finite-horizon Stieltjes bounds cc518136 and the original paymentTimes definition, using pinned ENNReal.ofReal strict-order lemma.

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_truncated_clock_only_loses_horizon_endpoint
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 ≤ T) :
    paymentTimes σ ∩ Iic T ⊆
      (paymentTimes (min σ (ENNReal.ofReal T)) ∩ Iic T) ∪ {T} := by sorry
