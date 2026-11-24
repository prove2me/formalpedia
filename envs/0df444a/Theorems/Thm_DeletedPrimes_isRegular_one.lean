-- Prove2me | Theorems.Thm_DeletedPrimes_isRegular_one
-- name    : DeletedPrimes.isRegular_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:46.899799+00:00
-- url     : https://prove2.me/theorems/bbc03501-aacc-4ac0-a914-412b69da3c3d
-- title:
--   Deleted Primes: is Regular one
-- statement:
--   The Deleted Primes construction uses the is Regular one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L154-L156
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L154-L156

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.isRegular_one (S : Set ℕ) : IsRegular S 1 := by sorry
