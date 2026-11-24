-- Prove2me | Theorems.Thm_DeletedPrimes_errExp_one
-- name    : DeletedPrimes.errExp_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:02:56.223602+00:00
-- url     : https://prove2.me/theorems/e9f6564f-41de-4a19-abeb-5b9716d562ef
-- title:
--   Deleted Primes: err Exp one
-- statement:
--   The Deleted Primes construction uses the err Exp one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L144-L170
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L144-L170

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.errExp_one {α κ τ : ℝ} (hτ0 : 0 ≤ τ) (hτκ : τ ≤ κ) :
    errExp 1 α κ τ = (α - 1) + κ + τ * (1 - α) + min (α * κ) (κ - τ) - α * κ := by sorry
