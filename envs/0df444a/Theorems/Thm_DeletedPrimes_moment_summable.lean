-- Prove2me | Theorems.Thm_DeletedPrimes_moment_summable
-- name    : DeletedPrimes.moment_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:09:00.365811+00:00
-- url     : https://prove2.me/theorems/8e47b021-c999-4097-a188-b3f37dbf0bdb
-- title:
--   Deleted Primes: moment summable
-- statement:
--   Proposition 7.2: `∑_n n^{α−1−2b}` converges iff `α/2 < b`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L36-L38
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L36-L38

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.moment_summable {α b : ℝ} :
    Summable (fun n : ℕ => (n : ℝ) ^ (α - 1 - 2 * b)) ↔ α / 2 < b := by sorry
