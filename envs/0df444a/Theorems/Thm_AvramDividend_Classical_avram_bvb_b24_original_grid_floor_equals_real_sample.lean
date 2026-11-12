-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b24_original_grid_floor_equals_real_sample
-- name    : AvramDividend.Classical.avram_bvb_b24_original_grid_floor_equals_real_sample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:33:53.120594+00:00
-- url     : https://prove2.me/theorems/d1d0f8bd-1b34-49ce-a354-3cdd6cea9b5d
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
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b24_original_grid_floor_equals_real_sample
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
       (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n : ℕ) (t : ℝ) :
    u n ⌊(t / T) * ((n : ℝ) + 2)⌋₊ =
      Real.toNNReal
        (T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
          ((n : ℝ) + 2)) := by sorry
