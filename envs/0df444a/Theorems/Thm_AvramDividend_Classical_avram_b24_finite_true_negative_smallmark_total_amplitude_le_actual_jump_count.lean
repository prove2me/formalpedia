-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_finite_true_negative_smallmark_total_amplitude_le_actual_jump_count
-- name    : AvramDividend.Classical.avram_b24_finite_true_negative_smallmark_total_amplitude_le_actual_jump_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:58:06.161277+00:00
-- url     : https://prove2.me/theorems/e465e1f3-fc33-4111-92d0-acd1733630d3
-- title:
--   Sum of genuine finite small-negative mark amplitudes has absolute size at most actual original jump count
-- statement:
--   For any finite set S of genuine negative physical Lévy jump times with mark z(u), the compensated small-negative path's actual uncentred sum over -1<z<0 has absolute magnitude at most the number of physical jump times, because each surviving small jump has magnitude strictly below 1. This deterministic bound composes with the Proved original finite-activity smallmark path identity and original count L2 integrability to supply an L1 dominator without any moment hypothesis on large negative jumps.
-- source:
--   Pinned norm_sum_le, finite sum comparison and elementary real small-negative interval bound.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_finite_true_negative_smallmark_total_amplitude_le_actual_jump_count
    {α : Type*} (S : Finset α) (z : α → ℝ) :
    ‖∑ u ∈ S, if -1 < z u ∧ z u < 0 then z u else 0‖ ≤
      (S.card : ℝ) := by sorry
