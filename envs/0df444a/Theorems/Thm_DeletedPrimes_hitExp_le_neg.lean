-- Prove2me | Theorems.Thm_DeletedPrimes_hitExp_le_neg
-- name    : DeletedPrimes.hitExp_le_neg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:44:05.585321+00:00
-- url     : https://prove2.me/theorems/274ff553-a9f8-4f47-baee-8e7b57def419
-- title:
--   Deleted Primes: hit Exp le neg
-- statement:
--   The Deleted Primes construction uses the hit Exp le neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L79-L83
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L79-L83

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.hitExp_le_neg {k : ℕ} (hk : 1 ≤ k) {α κ u τ : ℝ} (hκu : κ = k * u) {i : ℕ} (hi : i ≤ k)
    (ha : κ - τ - i * u ≤ 0) : hitExp k α κ τ ≤ α * i * u := by sorry
