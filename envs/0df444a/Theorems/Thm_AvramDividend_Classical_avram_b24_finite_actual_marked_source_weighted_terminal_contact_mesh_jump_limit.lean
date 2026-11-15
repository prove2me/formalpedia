-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_finite_actual_marked_source_weighted_terminal_contact_mesh_jump_limit
-- name    : AvramDividend.Classical.avram_b24_finite_actual_marked_source_weighted_terminal_contact_mesh_jump_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:21:40.20121+00:00
-- url     : https://prove2.me/theorems/af99f7ce-d70b-44b5-a476-310c4417c709
-- title:
--   Bounded predictable physical ruin-contact compensated mark increment tends to the actual original surviving negative jump
-- statement:
--   For a genuine original finite-activity intrinsic compensated negative-smallmark path identified as the actual right-inclusive finite chronological marked step sum minus deterministic compensator drift, its bounded-weight physical last-cell increment across positive true contact time t converges to predictable weight Wleft times the unique genuine marked atom z(t) if t is a source jump and z(t) lies in (-1,0), and to zero otherwise. The physical mesh approaches t from strictly left and weakly right, preserving the ruin-crossing negative mark rather than incorrectly treating it as continuous Gaussian noise. Directly combines the Proved finite marked-step terminal atom and full weighted càdlàg contact filter limit.
-- source:
--   Proved B24 true original finite marked-step terminal left limit and weighted càdlàg physical contact limit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_finite_compensated_actual_marked_step_terminal_jump_right_left_exact
import Theorems.Thm_AvramDividend_Classical_avram_b24_terminal_compensated_mark_contact_increment_has_true_jump_limit
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_finite_actual_marked_source_weighted_terminal_contact_mesh_jump_limit
    (S : Finset ℝ≥0) (z : ℝ≥0 → ℝ) (d : ℝ)
    (Jsmall : ℝ≥0 → ℝ) (T t : ℝ≥0)
    (ht0 : 0 < t) (htT : t ≤ T)
    (hPath : ∀ v : ℝ≥0, v ≤ T →
      Jsmall v =
        (∑ u ∈ S,
          if u ≤ v then (if -1 < z u ∧ z u < 0 then z u else 0) else 0) -
        (v : ℝ) * d)
    (hRight : ContinuousWithinAt Jsmall (Ici t) t)
    (a b : ℕ → ℝ≥0) (W : ℕ → ℝ) (Wleft : ℝ)
    (ha : Tendsto a atTop (𝓝[<] t))
    (hb : Tendsto b atTop (𝓝[Ici t] t))
    (hW : Tendsto W atTop (𝓝 Wleft)) :
    Tendsto (fun k => W k * (Jsmall (b k) - Jsmall (a k))) atTop
      (𝓝 (Wleft * (if t ∈ S then
        (if -1 < z t ∧ z t < 0 then z t else 0) else 0))) := by sorry
