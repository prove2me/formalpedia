-- Prove2me | Theorems.Thm_DeletedPrimes_muS_one
-- name    : DeletedPrimes.muS_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:01.770963+00:00
-- url     : https://prove2.me/theorems/c8dac1ea-dcdb-4668-a3f5-5824ca80e77e
-- title:
--   Deleted Primes: mu S one
-- statement:
--   The Deleted Primes construction uses the mu S one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L38-L39
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L38-L39

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.muS_one (S : Set ℕ) : muS S 1 = 1 := by sorry
