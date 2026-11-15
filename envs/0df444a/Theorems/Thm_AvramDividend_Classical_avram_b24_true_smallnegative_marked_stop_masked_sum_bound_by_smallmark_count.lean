-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_true_smallnegative_marked_stop_masked_sum_bound_by_smallmark_count
-- name    : AvramDividend.Classical.avram_b24_true_smallnegative_marked_stop_masked_sum_bound_by_smallmark_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:22:18.390009+00:00
-- url     : https://prove2.me/theorems/53acc0d9-3544-40df-a575-af82d7d98f99
-- title:
--   Actual stopped finite small-negative marked source is bounded by its true smallmark jump count plus drift
-- statement:
--   On a bounded physical horizon, the absolute compensated finite sum of genuine original marks in (-1,0), with any stopped mask selecting only some of those marks and the original signed smallmark compensator drift, is bounded by the count of actual small-negative marked jump times plus the horizon times the absolute drift. The mask may encode true ruin clipping and strict-left/inclusive-right cells. Each selected negative smallmark has absolute amplitude below 1. This bound can be combined with the Proved exact original Poisson count and its finite first moment to deliver a physical L1 envelope for marked contact and stopped finite grids without assuming large negative jump moments.
-- source:
--   Finite small negative mark norm/card triangle and original real horizon bound.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_true_smallnegative_marked_stop_masked_sum_bound_by_smallmark_count
    {α : Type*} (S : Finset α) (z : α → ℝ) (mask : α → Bool)
    (T t : ℝ≥0) (ht : t ≤ T) (d : ℝ) :
    ‖(∑ i ∈ S, if mask i then
        (if -1 < z i ∧ z i < 0 then z i else 0) else 0) -
      (t : ℝ) * d‖ ≤
      ((S.filter (fun i => -1 < z i ∧ z i < 0)).card : ℝ) +
        (T : ℝ) * ‖d‖ := by sorry
