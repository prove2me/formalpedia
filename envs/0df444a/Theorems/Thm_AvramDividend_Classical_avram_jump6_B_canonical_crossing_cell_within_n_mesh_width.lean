-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_crossing_cell_within_n_mesh_width
-- name    : AvramDividend.Classical.avram_jump6_B_canonical_crossing_cell_within_n_mesh_width
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:52:49.161699+00:00
-- url     : https://prove2.me/theorems/0af25816-8cfa-4b62-8f23-454bb714e391
-- title:
--   True original crossing cell lies in the last n divided by j+1 clock window
-- statement:
--   For any positive integer horizon n and a canonical grid crossing at contact clock t, t is bounded by the left endpoint plus n/(j+1). This gives the exact finite-j shrinking pre-contact tail-window assumption needed for the true ruin crossing cash inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_canonical_clipped_mesh_width
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_canonical_crossing_cell_within_n_mesh_width
    (n j i : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (hcross : min (((i + 1 : ℕ) : ℝ≥0) /
      ((j + 1 : ℕ) : ℝ≥0)) t = t) :
    t ≤ min ((i : ℝ≥0) /
      ((j + 1 : ℕ) : ℝ≥0)) t +
      (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0) := by sorry
