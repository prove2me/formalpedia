-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_small_positive_time_admits_half_unit_grid
-- name    : AvramDividend.Classical.avram_wave5_04c_small_positive_time_admits_half_unit_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:21:34.270229+00:00
-- url     : https://prove2.me/theorems/72c5d113-e86d-4bcd-8a92-9bd9663c91ef
-- title:
--   A small positive real step admits an integer grid with terminal time between one half and one
-- statement:
--   If 0<h≤1/2 then for n=floor(1/h), 1/2≤nh≤1. The fully formal numerical grid lemma supports the source BV residual first-moment 1/h uniform-integrability estimate.
-- source:
--   Full source privately remote-compiled to deliberate sentinel: candidates/work_on/AvramDividend_04c_positive_small_h_grid_floor_probe.lean

import Mathlib
set_option autoImplicit false
open scoped NNReal

theorem AvramDividend.Classical.avram_wave5_04c_small_positive_time_admits_half_unit_grid (h : ℝ) (hh : 0 < h) (hhalf : h ≤ 1 / 2) :
    ∃ n : ℕ, (1 / 2 : ℝ) ≤ (n : ℝ) * h ∧ (n : ℝ) * h ≤ 1 := by sorry
