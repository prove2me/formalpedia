-- Prove2me | Theorems.Thm_DeletedPrimes_theta_le_dim
-- name    : DeletedPrimes.theta_le_dim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:01:56.776605+00:00
-- url     : https://prove2.me/theorems/e27e08fc-c9b9-425b-891b-9024fb58a4ee
-- title:
--   Deleted Primes: theta le dim
-- statement:
--   `θ(S) ≤ α(S)` for every set of primes with `∑_{p ∈ S} 1/p < ∞`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L489-L499
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L489-L499

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.theta_le_dim (hS : ∀ p ∈ S, p.Prime)
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) :
    theta S ≤ dim S := by sorry
