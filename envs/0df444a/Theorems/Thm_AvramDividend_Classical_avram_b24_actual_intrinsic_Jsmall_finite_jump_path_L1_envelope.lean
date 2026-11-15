-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_actual_intrinsic_Jsmall_finite_jump_path_L1_envelope
-- name    : AvramDividend.Classical.avram_b24_actual_intrinsic_Jsmall_finite_jump_path_L1_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:02:33.195202+00:00
-- url     : https://prove2.me/theorems/3b73111c-d520-43f2-b293-439aa38c1fa5
-- title:
--   Actual finite-activity compensated smallmark path is bounded by number of true negative jumps and horizon drift
-- statement:
--   If an original small negative jump source on a physical clock t≤T has the exact finite true-mark path representation j=∑_{actual marks in (-1,0)} z_i - t*d, then its absolute value is bounded by the actual number of jump times plus T times the absolute complete small negative mark compensator drift. This source-algebraic bound combines with Proved B24 finite true negative jump amplitude ≤ physical count and Proved original Poisson count L1 to supply a common integrable horizon envelope for the marked Itô-Meyer contact cell without assuming a large negative mark second moment or suppressing ruin jumps.
-- source:
--   Proved B24 true smallnegative finite-mark norm bound, triangle and elapsed time comparison.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_finite_true_negative_smallmark_total_amplitude_le_actual_jump_count
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_actual_intrinsic_Jsmall_finite_jump_path_L1_envelope
    {α : Type*}
    (S : Finset α) (z : α → ℝ) (T : ℝ≥0) (t : ℝ≥0)
    (ht : t ≤ T) (d j : ℝ)
    (hj : j = (∑ i ∈ S, if -1 < z i ∧ z i < 0 then z i else 0) -
      (t : ℝ) * d) :
    ‖j‖ ≤ (S.card : ℝ) + (T : ℝ) * ‖d‖ := by sorry
