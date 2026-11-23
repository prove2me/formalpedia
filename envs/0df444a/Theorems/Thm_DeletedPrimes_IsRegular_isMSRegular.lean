-- Prove2me | Theorems.Thm_DeletedPrimes_IsRegular_isMSRegular
-- name    : DeletedPrimes.IsRegular.isMSRegular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:47:22.424481+00:00
-- url     : https://prove2.me/theorems/5cb2e330-2060-455a-9cea-2cb7e9c19b07
-- title:
--   Is Regular: is MSRegular
-- statement:
--   A sup-norm bound gives the same mean-square bound.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L214-L231
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L214-L231

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.IsRegular.isMSRegular {S : Set ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (h : IsRegular S θ) :
    IsMSRegular S θ := by sorry
