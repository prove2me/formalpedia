-- Prove2me | Theorems.Thm_DeletedPrimes_summable_muS_div
-- name    : DeletedPrimes.summable_muS_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:52:29.5958+00:00
-- url     : https://prove2.me/theorems/b0a03795-997c-4d30-a7db-e459b7d2279d
-- title:
--   Deleted Primes: summable mu S div
-- statement:
--   `∑_d μ_S(d)/d` converges absolutely when `∑_{p ∈ S} 1/p < ∞`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L282-L285
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L282-L285

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.summable_muS_div
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) :
    Summable fun d : ℕ => (muS S d : ℝ) / d := by sorry
