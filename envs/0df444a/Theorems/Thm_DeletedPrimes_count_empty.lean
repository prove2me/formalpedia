-- Prove2me | Theorems.Thm_DeletedPrimes_count_empty
-- name    : DeletedPrimes.count_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:57:12.915371+00:00
-- url     : https://prove2.me/theorems/0d12a19e-143f-44d2-8e60-cc8fa03ee062
-- title:
--   Deleted Primes: count empty
-- statement:
--   `N_∅(x) = ⌊x⌋`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L84-L89
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L84-L89

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.count_empty {x : ℝ} : count ∅ x = ⌊x⌋₊ := by sorry
