-- Prove2me | Theorems.Thm_DeletedPrimes_rankin_count
-- name    : DeletedPrimes.rankin_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:52:39.592665+00:00
-- url     : https://prove2.me/theorems/1c50d926-a011-48df-aec1-5645f2fc67fd
-- title:
--   Deleted Primes: rankin count
-- statement:
--   Rankin's bound (5.2) for the count: `#{d ≤ Z : d ∈ 𝒟_S} ≤ K(σ) Z^σ` for `σ ≥ 0` and `Z ≥ 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L314-L335
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L314-L335

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.rankin_count {σ : ℝ} (hsum : Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ))
    (hσ : 0 ≤ σ) {Z : ℝ} (hZ : 1 ≤ Z) :
    ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, |(muS S d : ℝ)| ≤ unitSum S σ * Z ^ σ := by sorry
