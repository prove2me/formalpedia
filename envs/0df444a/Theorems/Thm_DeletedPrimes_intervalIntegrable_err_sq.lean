-- Prove2me | Theorems.Thm_DeletedPrimes_intervalIntegrable_err_sq
-- name    : DeletedPrimes.intervalIntegrable_err_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:50:07.811044+00:00
-- url     : https://prove2.me/theorems/68b843ca-15d2-408d-a38e-1aad4440d683
-- title:
--   Deleted Primes: interval Integrable err sq
-- statement:
--   The Deleted Primes construction uses the interval Integrable err sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L122-L138
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L122-L138

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.intervalIntegrable_err_sq (S : Set ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x => err S x ^ 2) volume a b := by sorry
