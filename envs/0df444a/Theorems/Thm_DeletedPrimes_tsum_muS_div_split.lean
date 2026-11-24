-- Prove2me | Theorems.Thm_DeletedPrimes_tsum_muS_div_split
-- name    : DeletedPrimes.tsum_muS_div_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:03.630133+00:00
-- url     : https://prove2.me/theorems/4661796c-3d5d-4bb4-af51-fe732e48b1b9
-- title:
--   Deleted Primes: tsum mu S div split
-- statement:
--   Splitting `∑_d μ_S(d)/d` at `x`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L380-L417
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L380-L417

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.tsum_muS_div_split (hsum : Summable fun d : ℕ => (muS S d : ℝ) / d) (x : ℝ) :
    ∑' d : ℕ, (muS S d : ℝ) / d = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) / d
      + ∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0) := by sorry
