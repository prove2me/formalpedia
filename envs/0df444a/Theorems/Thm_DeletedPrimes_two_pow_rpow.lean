-- Prove2me | Theorems.Thm_DeletedPrimes_two_pow_rpow
-- name    : DeletedPrimes.two_pow_rpow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:49:13.243804+00:00
-- url     : https://prove2.me/theorems/0c6bf045-8773-46ac-8dad-e9eb339bf377
-- title:
--   Deleted Primes: two pow rpow
-- statement:
--   `(2^j)^a = (2^a)^j`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L38-L40
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L38-L40

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.two_pow_rpow (j : ℕ) (a : ℝ) : ((2 : ℝ) ^ j) ^ a = ((2 : ℝ) ^ a) ^ j := by sorry
