-- Prove2me | Theorems.Thm_DeletedPrimes_meanSq_le_of_pointwise
-- name    : DeletedPrimes.meanSq_le_of_pointwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:50:16.701207+00:00
-- url     : https://prove2.me/theorems/f4d5f41b-4593-4f99-b569-925eb67181f7
-- title:
--   Deleted Primes: mean Sq le of pointwise
-- statement:
--   The Deleted Primes construction uses the mean Sq le of pointwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L179-L191
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L179-L191

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.meanSq_le_of_pointwise {S : Set ℕ} {X M : ℝ} (hX : 1 ≤ X)
    (h : ∀ x ∈ Set.Icc X (2 * X), err S x ^ 2 ≤ M) : meanSq S X ≤ M := by sorry
