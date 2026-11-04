-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_uniform_mesh_tendsto
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_positive_uniform_mesh_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:45:11.21096+00:00
-- url     : https://prove2.me/theorems/f850b650-d25e-4f84-9b8a-85e9b5c5baff
-- title:
--   Positive original-grid mesh T/(n+1) tends to zero from the right
-- statement:
--   For any strictly positive finite nonnegative horizon T, the real grid mesh T/(n+1) tends to zero through positive values. This is the exact filter transport needed to specialise the already-Proved original-source O(h) negative-increment probability rate along the uniform mesh used by the pathwise P2-A jump-count liminf theorem.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_positive_uniform_mesh_tendsto
    (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n : ℕ => (T : ℝ) / ((n : ℝ) + 1))
      atTop (nhdsWithin (0 : ℝ) (Ioi 0)) := by sorry
