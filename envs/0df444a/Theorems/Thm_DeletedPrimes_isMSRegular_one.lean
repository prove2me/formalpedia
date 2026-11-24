-- Prove2me | Theorems.Thm_DeletedPrimes_isMSRegular_one
-- name    : DeletedPrimes.isMSRegular_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:50:34.605797+00:00
-- url     : https://prove2.me/theorems/fa75316f-54d8-482f-8625-620adc501c67
-- title:
--   Deleted Primes: is MSRegular one
-- statement:
--   The Deleted Primes construction uses the is MSRegular one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L233-L234
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L233-L234

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.isMSRegular_one (S : Set ℕ) : IsMSRegular S 1 := by sorry
