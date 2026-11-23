-- Prove2me | Theorems.Thm_DeletedPrimes_hitExp_le_pos
-- name    : DeletedPrimes.hitExp_le_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:43:59.210102+00:00
-- url     : https://prove2.me/theorems/ac83b44d-07fd-4907-9be8-1ad56749e764
-- title:
--   Deleted Primes: hit Exp le pos
-- statement:
--   The Deleted Primes construction uses the hit Exp le pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L73-L77
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L73-L77

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.hitExp_le_pos {k : ℕ} (hk : 1 ≤ k) {α κ u τ : ℝ} (hκu : κ = k * u) {i : ℕ} (hi : i ≤ k)
    (ha : 0 ≤ κ - τ - i * u) : hitExp k α κ τ ≤ α * i * u + (κ - τ - i * u) := by sorry
