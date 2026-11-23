-- Prove2me | Theorems.Thm_DeletedPrimes_kappaK_lt_half
-- name    : DeletedPrimes.kappaK_lt_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:44:10.897567+00:00
-- url     : https://prove2.me/theorems/7269a844-2fcd-4311-8889-bac23db7aeec
-- title:
--   Deleted Primes: kappa K lt half
-- statement:
--   The Deleted Primes construction uses the kappa K lt half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L181-L192
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L181-L192

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.kappaK_lt_half {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    kappaK k α < 1 / 2 := by sorry
