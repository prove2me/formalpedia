-- Prove2me | Theorems.Thm_DeletedPrimes_term_le
-- name    : DeletedPrimes.term_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:56:24.361794+00:00
-- url     : https://prove2.me/theorems/349bc789-a54a-4469-885f-ed5b079dd9df
-- title:
--   Deleted Primes: term le
-- statement:
--   The Deleted Primes construction uses the term le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L166-L174
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L166-L174

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.term_le {α : ℝ} (hα : 0 ≤ α) {p j : ℕ} (h1 : 2 ^ j ≤ p) (h2 : p < 2 * 2 ^ j) :
    Real.log p / (p : ℝ) ^ α ≤ ((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α := by sorry
