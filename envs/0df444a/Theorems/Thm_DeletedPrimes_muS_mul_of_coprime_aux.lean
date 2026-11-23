-- Prove2me | Theorems.Thm_DeletedPrimes_muS_mul_of_coprime_aux
-- name    : DeletedPrimes.muS_mul_of_coprime_aux
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:48:06.502492+00:00
-- url     : https://prove2.me/theorems/2421ca16-38e0-4f8c-a2c1-6050fedb0c83
-- title:
--   Deleted Primes: mu S mul of coprime aux
-- statement:
--   The Deleted Primes construction uses the mu S mul of coprime aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L64-L76
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L64-L76

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.muS_mul_of_coprime_aux {q d : ℕ} (h : Nat.Coprime q d) :
    muS S (q * d) = muS S q * muS S d := by sorry
