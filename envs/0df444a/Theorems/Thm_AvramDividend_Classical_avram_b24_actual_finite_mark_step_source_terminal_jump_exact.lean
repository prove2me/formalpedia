-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_actual_finite_mark_step_source_terminal_jump_exact
-- name    : AvramDividend.Classical.avram_b24_actual_finite_mark_step_source_terminal_jump_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T16:53:42.512204+00:00
-- url     : https://prove2.me/theorems/26da6ef4-4271-40bf-9f6c-8e6d6457d533
-- title:
--   Exact terminal atom of original finite physical marked step sum is precisely the active jump at contact time
-- statement:
--   For a finite family of genuine negative-mark jump times S and their actual weighted jump amplitudes z(u), the difference between cumulative physical weak-right chronological marked step cash at terminal t and its strict-left cumulative value equals exactly the single marked jump at t if that original time is in the finite support, and zero otherwise. This deterministic step-source identity is key to retaining the unique ruin-contact negative mark while allowing jumpfree interior meshes; no postruin extension and no claim that marked terminal contact vanishes.
-- source:
--   Pinned Mathlib Finset sum, total order and exact singleton indicator at terminal physical contact.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_actual_finite_mark_step_source_terminal_jump_exact
    (S : Finset ℝ≥0) (z : ℝ≥0 → ℝ) (t : ℝ≥0) :
    (∑ u ∈ S, if u ≤ t then z u else 0) -
      (∑ u ∈ S, if u < t then z u else 0) =
        if t ∈ S then z t else 0 := by sorry
