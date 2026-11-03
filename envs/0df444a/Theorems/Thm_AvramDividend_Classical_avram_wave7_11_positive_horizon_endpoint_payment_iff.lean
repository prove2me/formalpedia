-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_horizon_endpoint_payment_iff
-- name    : AvramDividend.Classical.avram_wave7_11_positive_horizon_endpoint_payment_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:07:17.527577+00:00
-- url     : https://prove2.me/theorems/98c71508-1c0d-4483-a122-8be2b1e87e02
-- title:
--   Positive finite endpoint belongs to original dividend payment set iff ruin clock is later
-- statement:
--   For every positive real observation time T, the canonical source paymentTimes σ contains the terminal time T exactly when ENNReal.ofReal T < σ. This isolates the terminal dividend atom condition; the strict clock stopping convention excludes a dividend at the ruin instant, while a dividend at finite T before ruin is included by Iic T.
-- source:
--   Exact source definition of paymentTimes, for the endpoint-atom decomposition required by UBV finite-horizon value verification cc518136.

import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_positive_horizon_endpoint_payment_iff
    (σ : ℝ≥0∞) (T : ℝ) (hT : 0 < T) :
    T ∈ paymentTimes σ ↔ ENNReal.ofReal T < σ := by sorry
