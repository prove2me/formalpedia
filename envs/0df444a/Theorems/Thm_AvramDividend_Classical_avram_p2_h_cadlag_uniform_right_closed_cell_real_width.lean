-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_right_closed_cell_real_width
-- name    : AvramDividend.Classical.avram_p2_h_cadlag_uniform_right_closed_cell_real_width
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:45:14.138702+00:00
-- url     : https://prove2.me/theorems/56df36fc-a131-494c-aa57-9234cfec7128
-- title:
--   Every original right-closed uniform time cell has exact real width T/(n+1)
-- statement:
--   The difference between the real coordinates of consecutive NNReal uniform-grid endpoints is exactly T/(n+1), independently of the cell index, including index zero and all horizon-end cells.

import Mathlib

namespace AvramDividend.Classical
end AvramDividend.Classical

open Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_h_cadlag_uniform_right_closed_cell_real_width
    (T : ℝ≥0) (n j : ℕ) :
    (((((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) : ℝ) -
      (((j : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) : ℝ)) =
    (T : ℝ) / ((n : ℝ) + 1) := by sorry
