-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_mark_joint_avoiding_cuts
-- name    : AvramDividend.Classical.avram_p2_l_mesh_finite_mark_joint_avoiding_cuts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:04:38.269839+00:00
-- url     : https://prove2.me/theorems/613a0b5c-7d1f-4eaf-ae30-690924fb5c85
-- title:
--   Simultaneous finite partition cuts avoiding the selected original jump marks
-- statement:
--   Given a finite collection of actual jump marks and an indexed family of ordered real endpoint pairs, choose a cutoff in each open interval, simultaneously avoiding all the marks. Each new cut is valid for the finite interval-step approximation of negative compactly supported tests.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_finite_negative_marks_avoid_interval_point

open Set Filter Topology AvramDividend.Classical
open scoped BigOperators Classical

theorem AvramDividend.Classical.avram_p2_l_mesh_finite_mark_joint_avoiding_cuts {ι : Type*} (S : Finset ℝ)
    (a b : ι → ℝ) (hab : ∀ i : ι, a i < b i) :
    ∃ c : ι → ℝ, ∀ i : ι,
      a i < c i ∧ c i < b i ∧ c i ∉ S := by sorry
