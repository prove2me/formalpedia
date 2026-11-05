-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_mark_free_compact_left_boundary
-- name    : AvramDividend.Classical.avram_p2_l_mesh_mark_free_compact_left_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T11:01:09.710455+00:00
-- url     : https://prove2.me/theorems/dae42cbc-d4ac-4c6a-bb98-815844efbc4b
-- title:
--   Select a mark-free left boundary strictly outside the compact support of a real jump test
-- statement:
--   For a compactly supported real marked test and any finite set of actual intrinsic jump marks, choose a leftmost real partition cut outside the mark set such that the entire closed left half-line through the cut has zero test value. This establishes the first-cut condition needed to make finite interval-step approximations globally accurate without assuming atom-free predetermined cutoffs.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_left_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_marks_avoid_interval_point

open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_mark_free_compact_left_boundary
    (S : Finset ℝ) (f : ℝ → ℝ) (hfcomp : HasCompactSupport f) :
    ∃ A : ℝ, A ∉ S ∧ ∀ z : ℝ, z ≤ A → f z = 0 := by sorry
