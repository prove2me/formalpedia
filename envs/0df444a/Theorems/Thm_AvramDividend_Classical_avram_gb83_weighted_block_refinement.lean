-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb83_weighted_block_refinement
-- name    : AvramDividend.Classical.avram_gb83_weighted_block_refinement
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:51:18.300236+00:00
-- url     : https://prove2.me/theorems/fdf570c2-610d-46a0-ba93-306ebf60d464
-- title:
--   Weighted telescoping differences regroup over equal integer blocks
-- statement:
--   For any real path sampled at integer times, a weighted sum of increments over m+1 coarse blocks of b fine steps equals the weighted sum of all fine increments, where the weight for fine step r is that of parent block floor(r/b). This purely finite algebraic identity is the critical combinatorial component of gb82, the original Gaussian two-grid common-refinement identity.

import Mathlib

theorem AvramDividend.Classical.avram_gb83_weighted_block_refinement
    (m b : ℕ) (hb : 0 < b) (f g : ℕ → ℝ) :
    (Finset.range (m + 1)).sum (fun i =>
      g i * (f ((i + 1) * b) - f (i * b))) =
    (Finset.range ((m + 1) * b)).sum (fun r =>
      g (r / b) * (f (r + 1) - f r)) := by sorry
