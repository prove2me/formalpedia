-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b24_original_uniform_floor_A_integral_restrict_horizon
-- name    : AvramDividend.Classical.avram_bvb_b24_original_uniform_floor_A_integral_restrict_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:28:02.549867+00:00
-- url     : https://prove2.me/theorems/20fa094c-9980-4d27-b846-4f4e34fe0f15
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

theorem AvramDividend.Classical.avram_bvb_b24_original_uniform_floor_A_integral_restrict_horizon
    (T : ℝ) (hT : 0 < T) (n : ℕ) (c : ℕ → ℝ) :
    (∫ t : ℝ, if 0 ≤ t ∧
        t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
          c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0) =
    (∫ t in Icc 0 T, if 0 ≤ t ∧
        t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2) then
          c ⌊(t / T) * ((n : ℝ) + 2)⌋₊ else 0) := by sorry
