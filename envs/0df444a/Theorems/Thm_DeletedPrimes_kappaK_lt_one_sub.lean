-- Prove2me | Theorems.Thm_DeletedPrimes_kappaK_lt_one_sub
-- name    : DeletedPrimes.kappaK_lt_one_sub
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:49:04.112853+00:00
-- url     : https://prove2.me/theorems/f39d0f1c-2121-4296-96f0-d4b1afbec72f
-- title:
--   Deleted Primes: kappa K lt one sub
-- statement:
--   The Deleted Primes construction uses the kappa K lt one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L194-L204
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L194-L204

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.kappaK_lt_one_sub {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    kappaK k α < 1 - α := by sorry
