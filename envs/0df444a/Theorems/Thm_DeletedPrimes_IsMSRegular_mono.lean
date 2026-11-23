-- Prove2me | Theorems.Thm_DeletedPrimes_IsMSRegular_mono
-- name    : DeletedPrimes.IsMSRegular.mono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:45:52.934214+00:00
-- url     : https://prove2.me/theorems/b1b41a8c-b46e-4d63-98f1-b15890026044
-- title:
--   Is MSRegular: mono
-- statement:
--   The Is MSRegular construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L206-L211
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L206-L211

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.IsMSRegular.mono {S : Set ℕ} {θ θ' : ℝ} (h : IsMSRegular S θ) (hθ : θ ≤ θ') :
    IsMSRegular S θ' := by sorry
