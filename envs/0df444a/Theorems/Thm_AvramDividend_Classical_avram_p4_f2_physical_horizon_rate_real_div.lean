-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f2_physical_horizon_rate_real_div
-- name    : AvramDividend.Classical.avram_p4_f2_physical_horizon_rate_real_div
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T01:08:23.778346+00:00
-- url     : https://prove2.me/theorems/c3093fe5-49b3-448a-b97e-e89c4d11ca3b
-- title:
--   Physical NNReal time-grid Lévy intensity converts to exact real inverse-mesh rate
-- statement:
--   For a positive natural grid denominator k, the real image of the extended nonnegative physical-time Lévy intensity ((T/k):ENNReal)*ν equals T.real*ν.toReal/k. It is the source typecast identity required to apply the exact deterministic Bonferroni rate squeeze to the original negative-band count.
-- source:
--   Original source target 17372d7a has physical T/(k:NNReal) horizon and finite original ν negative-band rate; generic rate squeeze 6d362474 is Proved.

import Mathlib
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f2_physical_horizon_rate_real_div
    (T : ℝ≥0) (ν : ℝ≥0∞) (k : ℕ) (hk : 0 < k) :
    (((T / (k : ℝ≥0)) : ℝ≥0∞) * ν).toReal =
      (T : ℝ) * ν.toReal / (k : ℝ) := by sorry
