-- Prove2me | Theorems.Thm_DeletedPrimes_theta2_le_of_isMSRegular
-- name    : DeletedPrimes.theta2_le_of_isMSRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:50:54.9079+00:00
-- url     : https://prove2.me/theorems/a6d12bd6-5377-4f49-898a-c01c2e580a91
-- title:
--   Deleted Primes: theta2 le of is MSRegular
-- statement:
--   The Deleted Primes construction uses the theta2 le of is MSRegular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L250-L252
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L250-L252

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.theta2_le_of_isMSRegular {S : Set ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h : IsMSRegular S θ) :
    theta2 S ≤ θ := by sorry
