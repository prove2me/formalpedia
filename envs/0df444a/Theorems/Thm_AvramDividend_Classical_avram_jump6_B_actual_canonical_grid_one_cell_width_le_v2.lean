-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_grid_one_cell_width_le_v2
-- name    : AvramDividend.Classical.avram_jump6_B_actual_canonical_grid_one_cell_width_le_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:06:52.513182+00:00
-- url     : https://prove2.me/theorems/9019de52-711f-4e93-93dd-cf2b4cc0a545
-- title:
--   Exact original Avram clipped physical grid cell length bounded by mesh width
-- statement:
--   Every interval of the original clipped physical grid v(k)=min(k/(j+1),t) has width at most 1/(j+1), uniformly in the actual stopped time t, including the final ruin-contact cell. This deterministic lemma is necessary for controlling the original last mesh cell without introducing a fictitious process or stopping time.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_actual_canonical_grid_one_cell_width_le_v2
    (j i : ℕ) (t : ℝ≥0) :
    let v : ℕ → ℝ≥0 :=
      fun k => min ((k : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    v (i + 1) ≤ v i + (1 : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) := by sorry
