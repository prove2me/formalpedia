-- Prove2me | Theorems.Thm_DeletedPrimes_intervalIntegrable_count
-- name    : DeletedPrimes.intervalIntegrable_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:49:53.148799+00:00
-- url     : https://prove2.me/theorems/48131075-13f4-4077-84a1-d8fa4a23ca77
-- title:
--   Deleted Primes: interval Integrable count
-- statement:
--   The Deleted Primes construction uses the interval Integrable count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L105-L108
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L105-L108

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.intervalIntegrable_count (S : Set ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => (count S x : ℝ)) volume a b := by sorry
