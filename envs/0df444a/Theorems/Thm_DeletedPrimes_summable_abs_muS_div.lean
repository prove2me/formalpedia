-- Prove2me | Theorems.Thm_DeletedPrimes_summable_abs_muS_div
-- name    : DeletedPrimes.summable_abs_muS_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:48.628808+00:00
-- url     : https://prove2.me/theorems/2c0d6331-fb69-4316-bafa-89aa2c077b60
-- title:
--   Deleted Primes: summable abs mu S div
-- statement:
--   `∑_d |μ_S(d)/d| < ∞` when `∑_{p ∈ S} 1/p < ∞`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L274-L279
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L274-L279

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.summable_abs_muS_div
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) :
    Summable fun d : ℕ => |(muS S d : ℝ) / d| := by sorry
