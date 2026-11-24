-- Prove2me | Theorems.Thm_DeletedPrimes_theta2_set_one_mem
-- name    : DeletedPrimes.theta2_set_one_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:47:29.855942+00:00
-- url     : https://prove2.me/theorems/461c48b1-b2fe-4cc1-9692-3dd6ebd3cde7
-- title:
--   Deleted Primes: theta2 set one mem
-- statement:
--   The Deleted Primes construction uses the theta2 set one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L239-L240
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L239-L240

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.theta2_set_one_mem (S : Set ℕ) : (1 : ℝ) ∈ {θ : ℝ | 0 ≤ θ ∧ IsMSRegular S θ} := by sorry
