-- Prove2me | Theorems.Thm_DeletedPrimes_errExp_argmax
-- name    : DeletedPrimes.errExp_argmax
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:54:13.232956+00:00
-- url     : https://prove2.me/theorems/ea5e40f5-ed47-43a6-8218-a46c057cec77
-- title:
--   Deleted Primes: err Exp argmax
-- statement:
--   The Deleted Primes construction uses the err Exp argmax property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L270-L313
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L270-L313

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.errExp_argmax {k : ℕ} (hk : 1 ≤ k) {α κ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hκ : 0 ≤ κ) :
    errExp k α κ (argmaxExp k α κ) = maxExp k α κ := by sorry
