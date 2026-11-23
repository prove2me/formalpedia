-- Prove2me | Theorems.Thm_DeletedPrimes_term_u
-- name    : DeletedPrimes.term_u
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:44:02.478908+00:00
-- url     : https://prove2.me/theorems/66ac4fa4-95d0-4a56-a6fe-9907c14a28c2
-- title:
--   Deleted Primes: term u
-- statement:
--   The terms of `hitExp` written with the unit `u = κ/k`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L66-L71
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L66-L71

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.term_u {k : ℕ} (hk : 1 ≤ k) {α κ u τ : ℝ} (hκu : κ = k * u) (i : ℕ) :
    α * κ * i / k + max (κ - τ - κ * i / k) 0 = α * i * u + max (κ - τ - i * u) 0 := by sorry
