-- Prove2me | Theorems.Thm_DeletedPrimes_theta_set_one_mem
-- name    : DeletedPrimes.theta_set_one_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:45:49.421925+00:00
-- url     : https://prove2.me/theorems/184bfe42-be35-446c-9cea-01cb20f47ead
-- title:
--   Deleted Primes: theta set one mem
-- statement:
--   The Deleted Primes construction uses the theta set one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L161-L162
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L161-L162

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.theta_set_one_mem (S : Set ℕ) : (1 : ℝ) ∈ {θ : ℝ | 0 ≤ θ ∧ IsRegular S θ} := by sorry
