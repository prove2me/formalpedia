-- Prove2me | Theorems.Thm_DeletedPrimes_kappaK_mono
-- name    : DeletedPrimes.kappaK_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:05:01.963709+00:00
-- url     : https://prove2.me/theorems/d3fdc47f-8f08-4362-94f7-cfa84b936674
-- title:
--   Deleted Primes: kappa K mono
-- statement:
--   The Deleted Primes construction uses the kappa K mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L373-L386
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L373-L386

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.kappaK_mono {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {k k' : ℕ} (hk : 1 ≤ k) (hkk' : k ≤ k') :
    kappaK k α ≤ kappaK k' α := by sorry
