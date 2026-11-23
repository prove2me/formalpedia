-- Prove2me | Theorems.Thm_DeletedPrimes_IsRegular_nonneg_const
-- name    : DeletedPrimes.IsRegular.nonneg_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:45:59.07395+00:00
-- url     : https://prove2.me/theorems/cc50e180-dbf6-40fa-b57d-a063fac7a065
-- title:
--   Is Regular: nonneg const
-- statement:
--   The Is Regular construction uses the nonneg const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L142-L146
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L142-L146

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.IsRegular.nonneg_const {S : Set ℕ} {θ C : ℝ} (h : ∀ x : ℝ, 1 ≤ x → |err S x| ≤ C * x ^ θ) :
    0 ≤ C := by sorry
