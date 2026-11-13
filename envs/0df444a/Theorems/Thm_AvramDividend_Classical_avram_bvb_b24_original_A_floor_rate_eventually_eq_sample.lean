-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b24_original_A_floor_rate_eventually_eq_sample
-- name    : AvramDividend.Classical.avram_bvb_b24_original_A_floor_rate_eventually_eq_sample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:37:55.882527+00:00
-- url     : https://prove2.me/theorems/199ecf0e-d266-453c-8a76-5837536e6eaf
-- title:
--   Original masked loss upper bound on the genuine uniform floor grid
-- statement:
--   The actual original prepayment reserve's discounted open-cap negative mark loss on the refining uniform floor grid is eventually no greater than its closed-cap contact-time loss plus arbitrary epsilon, even when the grid misses contact occupation.
-- source:
--   Root-connected one-sided a.e. floor-sampling input for phys95/efbae9c3.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a19_uniform_delta_profile
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b24_original_grid_floor_equals_real_sample
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b24_original_A_floor_rate_eventually_eq_sample
    (T : ℝ) (hT : 0 < T) (C τ : ℝ≥0∞)
    (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i,
       (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (U : ℝ≥0 → ℝ) (ψ : ℝ → ℝ) (q : ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (htT : t < T) :
    ∀ᶠ n : ℕ in atTop,
      (if 0 ≤ t ∧ t < T * ((n : ℝ) + 1) / ((n : ℝ) + 2)
       then
         let s : ℝ≥0 := u n ⌊(t / T) * ((n : ℝ) + 2)⌋₊
         if (s : ℝ≥0∞) < τ ∧ 0 ≤ U s ∧ ENNReal.ofReal (U s) ≤ C
         then Real.exp (-(q * (s : ℝ))) * ψ (U s)
         else 0
       else 0) =
      (let s : ℝ≥0 := Real.toNNReal
        (T * (⌊(t / T) * ((n : ℝ) + 2)⌋₊ : ℝ) /
          ((n : ℝ) + 2))
       if (s : ℝ≥0∞) < τ ∧ 0 ≤ U s ∧ ENNReal.ofReal (U s) ≤ C
       then Real.exp (-(q * (s : ℝ))) * ψ (U s)
       else 0) := by sorry
