-- Prove2me | Theorems.Thm_DeletedPrimes_summable_units
-- name    : DeletedPrimes.summable_units
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:52:36.792246+00:00
-- url     : https://prove2.me/theorems/60d3d330-8899-47f1-9c97-66f3eb9dd548
-- title:
--   Deleted Primes: summable units
-- statement:
--   For every `σ > α(S)` the squarefree `S`-units have `∑_{d ∈ 𝒟_S} d^{−σ} < ∞`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L259-L271
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L259-L271

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.summable_units {σ : ℝ} (hσ : dim S < σ) :
    Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) := by sorry
