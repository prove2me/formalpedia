-- Prove2me | Theorems.Thm_DeletedPrimes_sum_divisors_muS
-- name    : DeletedPrimes.sum_divisors_muS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:58:43.353995+00:00
-- url     : https://prove2.me/theorems/507e93d2-ee68-4853-960c-5c134b214c97
-- title:
--   Deleted Primes: sum divisors mu S
-- statement:
--   `1_{𝒩_S}(n) = ∑_{d ∣ n} μ_S(d)` for `n ≥ 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L147-L152
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L147-L152

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.sum_divisors_muS (hS : ∀ p ∈ S, p.Prime) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, muS S d = if SFree S n then 1 else 0 := by sorry
