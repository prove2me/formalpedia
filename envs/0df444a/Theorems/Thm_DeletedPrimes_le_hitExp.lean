-- Prove2me | Theorems.Thm_DeletedPrimes_le_hitExp
-- name    : DeletedPrimes.le_hitExp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:26.327941+00:00
-- url     : https://prove2.me/theorems/986e9573-4aff-4599-993b-8db70635c59c
-- title:
--   Deleted Primes: le hit Exp
-- statement:
--   A lower bound for every term is a lower bound for `hitExp`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L61-L63
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L61-L63

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.le_hitExp {k : ℕ} {α κ τ c : ℝ}
    (h : ∀ i ≤ k, c ≤ α * κ * i / k + max (κ - τ - κ * i / k) 0) : c ≤ hitExp k α κ τ := by sorry
