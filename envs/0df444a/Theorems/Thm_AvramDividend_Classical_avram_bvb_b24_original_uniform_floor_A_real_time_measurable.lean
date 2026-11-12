-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b24_original_uniform_floor_A_real_time_measurable
-- name    : AvramDividend.Classical.avram_bvb_b24_original_uniform_floor_A_real_time_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:31:02.353205+00:00
-- url     : https://prove2.me/theorems/d69e8860-f460-492c-8ea4-baefe5a84f05
-- title:
--   Original masked loss upper bound on the genuine uniform floor grid
-- statement:
--   The actual original prepayment reserve's discounted open-cap negative mark loss on the refining uniform floor grid is eventually no greater than its closed-cap contact-time loss plus arbitrary epsilon, even when the grid misses contact occupation.
-- source:
--   Root-connected one-sided a.e. floor-sampling input for phys95/efbae9c3.

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b24_original_uniform_floor_A_real_time_measurable
    (T : ℝ) (n : ℕ) (c : ℕ → ℝ) :
    Measurable (fun t : ℝ =>
      if 0 ≤ t ∧
         t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
        c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0) := by sorry
