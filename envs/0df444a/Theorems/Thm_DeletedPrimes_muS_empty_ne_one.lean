-- Prove2me | Theorems.Thm_DeletedPrimes_muS_empty_ne_one
-- name    : DeletedPrimes.muS_empty_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:57:06.437995+00:00
-- url     : https://prove2.me/theorems/71f64e60-90e6-490c-a4ad-b3d9d2e34aeb
-- title:
--   Deleted Primes: mu S empty ne one
-- statement:
--   `μ_∅(d) = 0` for `d ≠ 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L92-L101
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L92-L101

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.muS_empty_ne_one {d : ℕ} (hd : d ≠ 1) : muS ∅ d = 0 := by sorry
