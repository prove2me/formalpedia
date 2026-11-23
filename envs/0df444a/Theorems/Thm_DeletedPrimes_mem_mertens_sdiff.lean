-- Prove2me | Theorems.Thm_DeletedPrimes_mem_mertens_sdiff
-- name    : DeletedPrimes.mem_mertens_sdiff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:49:20.963232+00:00
-- url     : https://prove2.me/theorems/90cf360c-1563-4d49-adc2-6e69e8b83a41
-- title:
--   Deleted Primes: mem mertens sdiff
-- statement:
--   The Deleted Primes construction uses the mem mertens sdiff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L122-L131
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L122-L131

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.mem_mertens_sdiff {S : Set ℕ} {a b : ℝ} (ha : 0 ≤ a) {p : ℕ}
    (hp : p ∈ (Finset.Icc 1 ⌊b⌋₊).filter (· ∈ S) \ (Finset.Icc 1 ⌊a⌋₊).filter (· ∈ S)) :
    p ∈ S ∧ 1 ≤ p ∧ a < p ∧ (p : ℝ) ≤ b := by sorry
