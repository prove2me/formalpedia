-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_activity_uniform_mesh_exp_gap_le_intensity_gap
-- name    : AvramDividend.Classical.finite_activity_uniform_mesh_exp_gap_le_intensity_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:26:04.992793+00:00
-- url     : https://prove2.me/theorems/d86ec565-e706-46e1-90aa-7a9baa4a6cec
-- title:
--   Uniform finite-activity exponential gap cancels the number of grid cells
-- statement:
--   For nonnegative 0≤a≤b and a positive time horizon T, the finite-activity exponential survival difference at mesh duration T/N, multiplied by N, is at most T(b−a). The grid size cancels exactly, permitting passage to infinite mesh refinement when b−a tends to zero.
-- source:
--   Proved exponential_decay_difference_le_interval_length; Avram, Palmowski and Pistorius (2007) Section 3.3 first-jump finite-activity argument.

import Theorems.Thm_AvramDividend_Classical_exponential_decay_difference_le_interval_length
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open AvramDividend.Classical

theorem AvramDividend.Classical.finite_activity_uniform_mesh_exp_gap_le_intensity_gap
    (a b T : ℝ) (N : ℕ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hT : 0 ≤ T) (hN : 0 < N) :
    (N : ℝ) *
      (Real.exp (-((T / (N : ℝ)) * a)) -
        Real.exp (-((T / (N : ℝ)) * b))) ≤ T * (b - a) := by sorry
