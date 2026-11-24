-- Prove2me | Theorems.Thm_DeletedPrimes_rankin_tail
-- name    : DeletedPrimes.rankin_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:52:33.503404+00:00
-- url     : https://prove2.me/theorems/441db61d-0036-40b7-be14-4b1ef34af325
-- title:
--   Deleted Primes: rankin tail
-- statement:
--   Rankin's bound (5.2) for the tail: `∑_{d > Z, d ∈ 𝒟_S} 1/d ≤ K(σ) Z^{σ−1}` for `σ ≤ 1` and `Z ≥ 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L338-L366
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L338-L366

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.rankin_tail {σ : ℝ} (hsum : Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ))
    (hσ1 : σ ≤ 1) {Z : ℝ} (hZ : 1 ≤ Z) :
    ∑' d : ℕ, (if Z < d then |(muS S d : ℝ)| / d else 0) ≤ unitSum S σ * Z ^ (σ - 1) := by sorry
