-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb85_uniform_weighted_block_regroup
-- name    : AvramDividend.Classical.avram_gb85_uniform_weighted_block_regroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:56:07.093036+00:00
-- url     : https://prove2.me/theorems/76e5f1c3-8863-491a-869c-293271b17d97
-- title:
--   Regroup weighted range sums into equal quotient blocks
-- statement:
--   For b positive, a sum over the first (m+1)b fine indices with coefficient g(floor(r/b)) can be regrouped as a sum over coarse block index i of g(i) times the sum over b offsets within that block. This is an exact finite-sum index transformation and is one substantive input to the original common-refinement identity gb83, which also needs finite telescoping gb84.

import Mathlib

theorem AvramDividend.Classical.avram_gb85_uniform_weighted_block_regroup
    (m b : ℕ) (hb : 0 < b) (f : ℕ → ℝ) (g : ℕ → ℝ) :
    (Finset.range ((m + 1) * b)).sum (fun r => g (r / b) * f r) =
    (Finset.range (m + 1)).sum (fun i =>
      g i * (Finset.range b).sum (fun j => f (i * b + j))) := by sorry
