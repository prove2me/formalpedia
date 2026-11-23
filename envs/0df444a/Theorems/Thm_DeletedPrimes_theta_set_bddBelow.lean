-- Prove2me | Theorems.Thm_DeletedPrimes_theta_set_bddBelow
-- name    : DeletedPrimes.theta_set_bddBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:46:51.095808+00:00
-- url     : https://prove2.me/theorems/e61d00a7-a2b2-4091-8697-07012c0ce326
-- title:
--   Deleted Primes: theta set bdd Below
-- statement:
--   The Deleted Primes construction uses the theta set bdd Below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L158-L159
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L158-L159

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.theta_set_bddBelow (S : Set ℕ) : BddBelow {θ : ℝ | 0 ≤ θ ∧ IsRegular S θ} := by sorry
