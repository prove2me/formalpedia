-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_weighted_negative_mark_inverse_exact
-- name    : AvramDividend.Classical.avram_p2_b_rate_weighted_negative_mark_inverse_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:49:25.596604+00:00
-- url     : https://prove2.me/theorems/aac86bdb-5344-4baf-84a7-644e246dc2d3
-- title:
--   Exact cancellation of weighted exponential image test on strictly negative marks
-- statement:
--   For any strictly negative real jump mark y and arbitrary real test f, the fourth-power weight (exp y - 1)^4 multiplied by the inverse weighted logarithmic test evaluated at exp y equals f y. The negative-mark assumption ensures the denominator never vanishes. This source-free algebraic identity is the pointwise bridge needed when transferring the original weighted exponential derivative to compactly supported negative-mark tests.

import Mathlib
open MeasureTheory Set Filter Topology

theorem AvramDividend.Classical.avram_p2_b_rate_weighted_negative_mark_inverse_exact (f : ℝ → ℝ) (y : ℝ) (hy : y < 0) :
    (Real.exp y - 1) ^ 4 *
      (f (Real.log (Real.exp y)) / (Real.exp y - 1) ^ 4) = f y := by sorry
