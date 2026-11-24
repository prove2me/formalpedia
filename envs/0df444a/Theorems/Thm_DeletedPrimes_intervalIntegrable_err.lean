-- Prove2me | Theorems.Thm_DeletedPrimes_intervalIntegrable_err
-- name    : DeletedPrimes.intervalIntegrable_err
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:58:10.800384+00:00
-- url     : https://prove2.me/theorems/fe94570c-11ee-400c-8c9b-10bbc35dea8f
-- title:
--   Deleted Primes: interval Integrable err
-- statement:
--   The Deleted Primes construction uses the interval Integrable err property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L110-L114
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L110-L114

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.intervalIntegrable_err (S : Set ℕ) (a b : ℝ) :
    IntervalIntegrable (err S) volume a b := by sorry
