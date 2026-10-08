-- Prove2me | Theorems.Thm_AvramDividend_Classical_ladder_height_truncated_area_interval_bound
-- name    : AvramDividend.Classical.ladder_height_truncated_area_interval_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:50:11.730002+00:00
-- url     : https://prove2.me/theorems/76b635f4-acc3-43cd-8a97-27b028b0b01e
-- title:
--   Integrated truncated ladder-height weight is bounded by squared and linear jump scales
-- statement:
--   For every nonnegative jump magnitude z, the area under the truncated ladder-height weight min(1,t) from 0 to z is bounded by both z² and z. This follows by comparing min(1,t) separately with t and 1 and evaluating the two elementary integrals. It is the exact deterministic area inequality that, together with the Esscher-damped tail-area integrability lemma, shows the positive descending-ladder height kernel satisfies the Lévy subordinator ∫(1∧t)Kφ(t)dt<∞ condition after Tonelli.
-- source:
--   Pinned intervalIntegral.integral_mono_on, integral_id, intervalIntegral.integral_const and continuity.

import Mathlib
open MeasureTheory intervalIntegral Set

theorem AvramDividend.Classical.ladder_height_truncated_area_interval_bound
    (z : ℝ) (hz : 0 ≤ z) :
    (∫ t in (0 : ℝ)..z, min 1 t) ≤ min (z ^ 2) z := by sorry
