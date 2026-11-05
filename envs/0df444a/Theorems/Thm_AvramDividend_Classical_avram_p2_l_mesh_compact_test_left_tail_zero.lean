-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_l_mesh_compact_test_left_tail_zero
-- name    : AvramDividend.Classical.avram_p2_l_mesh_compact_test_left_tail_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:57:14.168394+00:00
-- url     : https://prove2.me/theorems/e93e21b3-66d4-40d5-8a87-7023fc89bc81
-- title:
--   Compact marked tests vanish below an original real support cut
-- statement:
--   Any compactly supported real marked-test function vanishes at every point below some real lower endpoint. It supplies the left tail bound needed for global finite interval-step approximation of compact negative tests without assuming a particular support radius.

import Mathlib

open Set Topology

theorem AvramDividend.Classical.avram_p2_l_mesh_compact_test_left_tail_zero (f : ℝ → ℝ) (hfcomp : HasCompactSupport f) : ∃ L : ℝ, ∀ z : ℝ, z < L → f z = 0 := by sorry
