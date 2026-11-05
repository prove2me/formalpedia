-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_avoid_marks_small_cutoff_tail
-- name    : AvramDividend.Classical.avram_p2_l_mesh_avoid_marks_small_cutoff_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:47:45.587676+00:00
-- url     : https://prove2.me/theorems/697d80ae-4bad-421f-8dd7-2d9457d80a68
-- title:
--   Avoid all selected marks with an error-small negative final cutoff
-- statement:
--   For a continuous test zero at its nominal negative cutoff and a finite set of actual jump marks, choose a strictly smaller final cutoff outside the finite mark set such that the test stays uniformly epsilon-small between the chosen cutoff and the original cutoff. This handles genuine cutoff atoms in the uniform finite-step approximation construction.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_marks_avoid_interval_point
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_continuous_test_small_left_cutoff_strip

open Set Topology AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_avoid_marks_small_cutoff_tail (S : Finset ℝ) (f : ℝ → ℝ) (ρ ε : ℝ) (hε : 0 < ε) (hfcont : ContinuousAt f (-ρ)) (hfzero : f (-ρ) = 0) : ∃ c : ℝ, c < -ρ ∧ c ∉ S ∧ ∀ z : ℝ, c ≤ z → z ≤ -ρ → |f z| < ε := by sorry
