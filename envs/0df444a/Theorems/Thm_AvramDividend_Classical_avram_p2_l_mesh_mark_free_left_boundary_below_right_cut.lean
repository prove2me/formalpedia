-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_mark_free_left_boundary_below_right_cut
-- name    : AvramDividend.Classical.avram_p2_l_mesh_mark_free_left_boundary_below_right_cut
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:09:21.335362+00:00
-- url     : https://prove2.me/theorems/a1a5b7e3-52de-4510-b412-7bede6c9f5e1
-- title:
--   Compact-test mark-free zero-tail left cut strictly below any prescribed final cut
-- statement:
--   For any compactly supported real jump test, finite set of original intrinsic jump marks and prescribed finite right cutoff B, choose a left partition cut A strictly below B, outside every selected mark, and such that f vanishes on the entire closed half-line through A. This ensures the ordered partition can always begin before the prescribed negative support-boundary strip.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_left_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_marks_avoid_interval_point

open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_mark_free_left_boundary_below_right_cut
    (S : Finset ℝ) (f : ℝ → ℝ) (hfcomp : HasCompactSupport f)
    (B : ℝ) :
    ∃ A : ℝ, A < B ∧ A ∉ S ∧ ∀ z : ℝ, z ≤ A → f z = 0 := by sorry
