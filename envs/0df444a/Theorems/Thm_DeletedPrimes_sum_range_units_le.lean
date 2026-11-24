-- Prove2me | Theorems.Thm_DeletedPrimes_sum_range_units_le
-- name    : DeletedPrimes.sum_range_units_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:51:51.158417+00:00
-- url     : https://prove2.me/theorems/91099cca-e749-4439-92ce-bd180ab17468
-- title:
--   Deleted Primes: sum range units le
-- statement:
--   Partial sums of `∑_{d ∈ 𝒟_S} d^{−σ}` are bounded by the partial Euler product `∏ (1 + p^{−σ})`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L186-L223
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L186-L223

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.sum_range_units_le (σ : ℝ) (N : ℕ) :
    ∑ d ∈ Finset.range N, |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) ≤
      ∏ p ∈ (Finset.range N).filter (· ∈ S), (1 + (p : ℝ) ^ (-σ)) := by sorry
