-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
-- name    : AvramDividend.Classical.chat03_clipped_grid_clock_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T05:23:39.558021+00:00
-- url     : https://prove2.me/theorems/9026f611-4ccd-4fcd-99a9-1dbc15752bd6
-- title:
--   A horizon-clipped uniform sampling clock is monotone and bounded
-- statement:
--   For any nonnegative horizon T and uniform-grid spacing h, the sampled clock j↦min(jh,T) is monotone in the natural grid index, begins at zero, and never exceeds T. It supplies the deterministic time-grid hypotheses for the accepted finite-horizon q-scale L² and expectation-convergence theorem.
-- source:
--   Use the order-preserving natural-number cast, nonnegative scalar multiplication, monotonicity of min, and min's elementary order bounds.

import Mathlib.Topology.Instances.ENNReal.Lemmas

open scoped NNReal

theorem AvramDividend.Classical.chat03_clipped_grid_clock_bounded
    (T h : ℝ≥0) :
    Monotone (fun j : ℕ => min ((j : ℝ≥0) * h) T) ∧
    (min ((0 : ℝ≥0) * h) T = 0) ∧
    (∀ j : ℕ, min ((j : ℝ≥0) * h) T ≤ T) := by
  sorry
