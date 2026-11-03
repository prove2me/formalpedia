-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_endpoint_not_in_min_clock
-- name    : AvramDividend.Classical.avram_wave7_11_positive_horizon_endpoint_not_in_min_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:54:07.595118+00:00
-- url     : https://prove2.me/theorems/5a47155e-c069-43c5-ad7a-3c3231167347
-- title:
--   Positive observation endpoint is excluded by strict payment clock min(σ,T)
-- statement:
--   For every positive real horizon T, the source paymentTimes of the truncated clock min(σ, ENNReal.ofReal T) excludes the payment time t=T. The first disjunct t=0 is false because T>0; the second would demand ENNReal.ofReal T < min(σ, ENNReal.ofReal T), impossible. This isolates the precise terminal dividend atom that may otherwise be lost in finite-horizon truncation.
-- source:
--   Exact canonical paymentTimes definition used by UBV finite-horizon verification cc518136; source-faithful terminal atom guard.

import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_positive_horizon_endpoint_not_in_min_clock
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 < T) :
    T ∉ paymentTimes (min σ (ENNReal.ofReal T)) := by sorry
