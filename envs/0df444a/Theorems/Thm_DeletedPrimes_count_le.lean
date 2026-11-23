-- Prove2me | Theorems.Thm_DeletedPrimes_count_le
-- name    : DeletedPrimes.count_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:49:33.052085+00:00
-- url     : https://prove2.me/theorems/f08467ce-0da0-4cd8-9a1b-3287301b0fdb
-- title:
--   Deleted Primes: count le
-- statement:
--   The Deleted Primes construction uses the count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L77-L84
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L77-L84

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.count_le (S : Set ℕ) {x : ℝ} (hx : 0 ≤ x) : (count S x : ℝ) ≤ x := by sorry
