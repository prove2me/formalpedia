-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva20_postruin_uniform_nat_floor_mask_eventually_false
-- name    : AvramDividend.Classical.avram_bva20_postruin_uniform_nat_floor_mask_eventually_false
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:13:45.428133+00:00
-- url     : https://prove2.me/theorems/0b378861-1773-4f41-b190-2ae59af5ca42
-- title:
--   Original natural-indexed uniform floor mask eventually vanishes strictly after ruin
-- statement:
--   The natural-number indexed uniform physical floor-grid samples approach a strictly post-ruin positive time in ENNReal and eventually exceed the ruin clock. Explicitly quantify the grid level n over Nat. This is the exact post-ruin mask input needed for the original compensator grid integral.
-- source:
--   Necessary natural-indexed postruin half of almost-everywhere grid mask convergence in 7ccc2a1a.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b21_original_uniform_floor_samples_converge_from_left
open Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva20_postruin_uniform_nat_floor_mask_eventually_false
    (T : ℝ) (hT : 0 < T) (t : ℝ≥0) (τ : ℝ≥0∞)
    (hτ : τ < (t : ℝ≥0∞)) :
    Filter.Eventually
      (fun n : ℕ => ¬ ((Real.toNNReal
        (T * (⌊(((t : ℝ) / T) * ((n : ℝ) + 2))⌋₊ : ℝ) /
          ((n : ℝ) + 2)) : ℝ≥0∞) < τ))
      Filter.atTop := by sorry
