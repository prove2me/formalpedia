-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below
-- name    : AvramDividend.Classical.avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T10:06:14.052697+00:00
-- url     : https://prove2.me/theorems/136fae3f-ad13-41b0-92c3-ab98822a937e
-- title:
--   Small reserve neighbourhood forces an arbitrarily negative original singular BV generator cell
-- statement:
--   For the original zero-extended affine BV singular generator profile, any strictly positive square-root reserve at most the square of a shrinking unit-horizon grid width produces a single signed generator cell no larger than minus the arbitrary integer K. The variable reserve is needed for stochastic perturbations of a deterministic tiny-surplus reset, not an unconditional counterexample.
-- source:
--   Quantitative original singular tail bound 23283bab with a variable small reserve and exact uniform physical-grid scaling; source-exact obstruction audit for 0b2da5b3.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_profile_tail_bound
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail11_singular_uniform_neighbourhood_unbounded_below
    (K : ℕ) (t : ℝ) (ht : 0 < t)
    (ht_bound : t ≤ (1 / ((K : ℝ) + 4)) ^ 2) :
    (1 / ((K : ℝ) + 4)) *
      (3 + t ^ 2 - 4 * t - 2 / t) ≤ -(K : ℝ) := by sorry
