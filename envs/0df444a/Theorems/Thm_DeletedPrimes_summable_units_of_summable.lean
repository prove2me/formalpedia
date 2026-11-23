-- Prove2me | Theorems.Thm_DeletedPrimes_summable_units_of_summable
-- name    : DeletedPrimes.summable_units_of_summable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:48:13.623812+00:00
-- url     : https://prove2.me/theorems/2e33d927-da6d-4d23-9464-cdbf76ddb9a9
-- title:
--   Deleted Primes: summable units of summable
-- statement:
--   The squarefree `S`-units have `∑_{d ∈ 𝒟_S} d^{−σ} < ∞` when `∑_{p ∈ S} p^{−σ} < ∞`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L226-L249
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L226-L249

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.summable_units_of_summable {σ : ℝ}
    (h : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-σ))) :
    Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) := by sorry
