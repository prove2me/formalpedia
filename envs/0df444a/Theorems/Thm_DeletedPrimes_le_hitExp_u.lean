-- Prove2me | Theorems.Thm_DeletedPrimes_le_hitExp_u
-- name    : DeletedPrimes.le_hitExp_u
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:44:14.752316+00:00
-- url     : https://prove2.me/theorems/190de3bb-757a-4a4e-a650-b967b46e309b
-- title:
--   Deleted Primes: le hit Exp u
-- statement:
--   The Deleted Primes construction uses the le hit Exp u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L85-L87
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L85-L87

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.le_hitExp_u {k : ℕ} (hk : 1 ≤ k) {α κ u τ c : ℝ} (hκu : κ = k * u)
    (h : ∀ i ≤ k, c ≤ α * i * u + max (κ - τ - i * u) 0) : c ≤ hitExp k α κ τ := by sorry
