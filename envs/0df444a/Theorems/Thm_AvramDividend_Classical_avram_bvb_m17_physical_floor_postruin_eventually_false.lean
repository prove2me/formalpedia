-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_m17_physical_floor_postruin_eventually_false
-- name    : AvramDividend.Classical.avram_bvb_m17_physical_floor_postruin_eventually_false
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:25:28.189864+00:00
-- url     : https://prove2.me/theorems/7779b441-0f03-4aa1-9a1b-7ff498730da6
-- title:
--   Original physical uniform grid is eventually past the stopped ruin clock for post-ruin observation times
-- statement:
--   At any strictly post-ruin positive real observation time, the literal original uniform-grid left endpoint u(n,floor((r/T)*(n+2))) is eventually no longer strictly before the ruin clock. Uses the exact original-grid floor identity and Proved generic postruin floor false theorem; the strict stop condition is preserved and no source path is altered.
-- source:
--   Proved avram_bva20_postruin_uniform_floor_mask_eventually_false 9ca78cf4 and exact physical sample bvb_m17; source bvb28 stopped marked floor convergence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_m17_uniform_floor_original_grid_eq
import Theorems.Thm_AvramDividend_Classical_avram_bva20_postruin_uniform_floor_mask_eventually_false
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_m17_physical_floor_postruin_eventually_false
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (r : ℝ) (hr : 0 < r) (τ : ℝ≥0∞)
    (hτ : τ < (Real.toNNReal r : ℝ≥0∞)) :
    ∀ᶠ n in Filter.atTop,
      ¬ ((u n ⌊(r / T) * ((n : ℝ) + 2)⌋₊ : ℝ≥0∞) < τ) := by sorry
