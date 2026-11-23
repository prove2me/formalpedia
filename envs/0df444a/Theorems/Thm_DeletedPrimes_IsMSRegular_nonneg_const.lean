-- Prove2me | Theorems.Thm_DeletedPrimes_IsMSRegular_nonneg_const
-- name    : DeletedPrimes.IsMSRegular.nonneg_const
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:47:36.047788+00:00
-- url     : https://prove2.me/theorems/183be47f-f633-433e-9da1-fb8ea6a477f2
-- title:
--   Is MSRegular: nonneg const
-- statement:
--   The Is MSRegular construction uses the nonneg const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L200-L204
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L200-L204

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.IsMSRegular.nonneg_const {S : Set ℕ} {θ C : ℝ}
    (h : ∀ X : ℝ, 1 ≤ X → meanSq S X ≤ C * X ^ (2 * θ)) : 0 ≤ C := by sorry
