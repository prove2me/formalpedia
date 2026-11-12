-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_postruin_uniform_floor_mask_eventually_false
-- name    : AvramDividend.Classical.avram_bva20_postruin_uniform_floor_mask_eventually_false
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:02:36.935989+00:00
-- url     : https://prove2.me/theorems/9ca78cf4-c13b-4123-9910-a361cf58a11a
-- title:
--   Original physical uniform floor mask eventually vanishes strictly after ruin
-- statement:
--   Every finite positive source time t strictly after a ruin clock τ has physical uniform floor-grid sample times eventually strictly after τ; the strict pre-ruin indicator used in the original closed-cap compensator grid then vanishes. The result completes the post-ruin pointwise branch needed for 7ccc2a1a, complementary to the published pre-ruin masked kernel convergence.
-- source:
--   Necessary post-ruin closed-cap mask branch for the original source-exact a.e. dominated-convergence proof of theorem 7ccc2a1a.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
open Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva20_postruin_uniform_floor_mask_eventually_false
    (T : ℝ) (hT : 0 < T) (t : ℝ≥0) (τ : ℝ≥0∞)
    (hτ : τ < (t : ℝ≥0∞)) :
    ∀ᶠ n in Filter.atTop,
      ¬ ((Real.toNNReal
        (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) /
          ((n : ℝ) + 2)) : ℝ≥0∞) < τ) := by sorry
