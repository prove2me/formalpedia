-- Prove2me | Theorems.Thm_DeletedPrimes_muS_mul_of_not_coprime
-- name    : DeletedPrimes.muS_mul_of_not_coprime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:59:37.566803+00:00
-- url     : https://prove2.me/theorems/db02db62-c76a-4296-a7b2-04a56cf975b4
-- title:
--   Deleted Primes: mu S mul of not coprime
-- statement:
--   Step 5 of §5: `qd' ∉ 𝒟_S` when `q ∈ 𝒟_S` and `d'` is not coprime to `q`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L176-L181
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L176-L181

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.muS_mul_of_not_coprime {q d : ℕ} (h : ¬ Nat.Coprime q d) : muS S (q * d) = 0 := by sorry
