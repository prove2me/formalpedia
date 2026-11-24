-- Prove2me | Theorems.Thm_DeletedPrimes_theta2_set_bddBelow
-- name    : DeletedPrimes.theta2_set_bddBelow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:50:31.979132+00:00
-- url     : https://prove2.me/theorems/38877921-febc-49a3-b20b-5516cf446559
-- title:
--   Deleted Primes: theta2 set bdd Below
-- statement:
--   The Deleted Primes construction uses the theta2 set bdd Below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L236-L237
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L236-L237

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.theta2_set_bddBelow (S : Set ℕ) : BddBelow {θ : ℝ | 0 ≤ θ ∧ IsMSRegular S θ} := by sorry
