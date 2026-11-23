-- Prove2me | Theorems.Thm_DeletedPrimes_maxExp_neg_iff
-- name    : DeletedPrimes.maxExp_neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:44:09.944117+00:00
-- url     : https://prove2.me/theorems/2cb2f07a-3194-4469-b052-db2ff2a1a285
-- title:
--   Deleted Primes: max Exp neg iff
-- statement:
--   The Deleted Primes construction uses the max Exp neg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L315-L325
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L315-L325

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.maxExp_neg_iff {k : ℕ} (hk : 1 ≤ k) {α κ : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    maxExp k α κ < 0 ↔ κ < kappaK k α := by sorry
