-- Prove2me | Theorems.Thm_DeletedPrimes_errExp_neg_iff
-- name    : DeletedPrimes.errExp_neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:03:28.109732+00:00
-- url     : https://prove2.me/theorems/ff9c6eb2-6e67-4512-b300-11992f13252d
-- title:
--   Deleted Primes: err Exp neg iff
-- statement:
--   Every error exponent on `[0, κ]` is negative iff `κ < κ_k(α)`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L328-L336
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L328-L336

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.errExp_neg_iff {k : ℕ} (hk : 1 ≤ k) {α κ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hκ : 0 ≤ κ) :
    (∀ τ ∈ Set.Icc 0 κ, errExp k α κ τ < 0) ↔ κ < kappaK k α := by sorry
