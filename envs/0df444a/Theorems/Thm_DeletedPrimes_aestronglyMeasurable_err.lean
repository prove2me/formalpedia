-- Prove2me | Theorems.Thm_DeletedPrimes_aestronglyMeasurable_err
-- name    : DeletedPrimes.aestronglyMeasurable_err
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:49:51.400687+00:00
-- url     : https://prove2.me/theorems/fff2105b-6b1d-4b04-b58b-f942f5fcf48a
-- title:
--   Deleted Primes: aestrongly Measurable err
-- statement:
--   The Deleted Primes construction uses the aestrongly Measurable err property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L116-L120
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L116-L120

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.aestronglyMeasurable_err (S : Set ℕ) : AEStronglyMeasurable (err S) volume := by sorry
