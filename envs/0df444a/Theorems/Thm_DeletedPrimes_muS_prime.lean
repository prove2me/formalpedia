-- Prove2me | Theorems.Thm_DeletedPrimes_muS_prime
-- name    : DeletedPrimes.muS_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:48:07.424532+00:00
-- url     : https://prove2.me/theorems/a48700fa-4f6c-46ba-b0a3-242e22da8da6
-- title:
--   Deleted Primes: mu S prime
-- statement:
--   The Deleted Primes construction uses the mu S prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L41-L42
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L41-L42

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.muS_prime {p : ℕ} (hp : p.Prime) : muS S p = if p ∈ S then -1 else 0 := by sorry
