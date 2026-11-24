-- Prove2me | Theorems.Thm_DeletedPrimes_split_total
-- name    : DeletedPrimes.split_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:09:26.125814+00:00
-- url     : https://prove2.me/theorems/872b8e83-82f2-45e8-9669-ee5ff04aad27
-- title:
--   Deleted Primes: split total
-- statement:
--   Proposition 7.3, step 4: `K^α + y^{1/2+4ε} K^{α−1} + y^{2ε} ≤ 3 y^{α/2+4ε}` for `K = y^{1/2}`, `y ≥ 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L48-L59
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L48-L59

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.split_total {y α ε : ℝ} (hy : 1 ≤ y) (hα : 0 ≤ α) (hε : 0 ≤ ε) :
    (y ^ (1 / 2 : ℝ)) ^ α + y ^ (1 / 2 + 4 * ε) * (y ^ (1 / 2 : ℝ)) ^ (α - 1) + y ^ (2 * ε)
      ≤ 3 * y ^ (α / 2 + 4 * ε) := by sorry
