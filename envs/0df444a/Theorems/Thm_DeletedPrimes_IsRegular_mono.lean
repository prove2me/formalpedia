-- Prove2me | Theorems.Thm_DeletedPrimes_IsRegular_mono
-- name    : DeletedPrimes.IsRegular.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:45:48.430542+00:00
-- url     : https://prove2.me/theorems/8c2c4cba-b53b-402c-ac3c-bec16711ee38
-- title:
--   Is Regular: mono
-- statement:
--   The Is Regular construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L148-L152
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L148-L152

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.IsRegular.mono {S : Set ℕ} {θ θ' : ℝ} (h : IsRegular S θ) (hθ : θ ≤ θ') : IsRegular S θ' := by sorry
