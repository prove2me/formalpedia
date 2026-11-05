-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_marks_avoid_interval_point
-- name    : AvramDividend.Classical.avram_p2_l_mesh_finite_negative_marks_avoid_interval_point
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:57:21.80848+00:00
-- url     : https://prove2.me/theorems/267ec85c-dca1-4d4a-87e5-c1f16e905c70
-- title:
--   Interior interval cutoff avoiding any finite set of original jump marks
-- statement:
--   For every finite set of intrinsic real jump marks and any two ordered real endpoints, there is a strictly interior cutoff that is not an intrinsic mark. The finite-set/density proof supplies the atom-avoiding partition endpoints needed to approximate a compactly supported negative test on a cadlag path.

import Mathlib

open Set Filter Topology

theorem AvramDividend.Classical.avram_p2_l_mesh_finite_negative_marks_avoid_interval_point (S : Finset ℝ) :
    ∀ a b : ℝ, a < b →
      ∃ c : ℝ, a < c ∧ c < b ∧ c ∉ S := by sorry
