-- Prove2me | Theorems.Thm_DeletedPrimes_muS_prime_pow
-- name    : DeletedPrimes.muS_prime_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:48:18.686485+00:00
-- url     : https://prove2.me/theorems/7893934c-200e-4484-8950-32938837c83f
-- title:
--   Deleted Primes: mu S prime pow
-- statement:
--   The Deleted Primes construction uses the mu S prime pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L44-L47
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L44-L47

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.muS_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) : muS S (p ^ k) = 0 := by sorry
