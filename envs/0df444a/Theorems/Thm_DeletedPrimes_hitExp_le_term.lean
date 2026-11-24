-- Prove2me | Theorems.Thm_DeletedPrimes_hitExp_le_term
-- name    : DeletedPrimes.hitExp_le_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:44:05.583212+00:00
-- url     : https://prove2.me/theorems/ae9c84bb-2950-4a62-8e32-e00ddac7321c
-- title:
--   Deleted Primes: hit Exp le term
-- statement:
--   `hitExp` is at most each of its terms.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L55-L58
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L55-L58

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.hitExp_le_term {k : ℕ} {α κ τ : ℝ} {i : ℕ} (hi : i ≤ k) :
    hitExp k α κ τ ≤ α * κ * i / k + max (κ - τ - κ * i / k) 0 := by sorry
