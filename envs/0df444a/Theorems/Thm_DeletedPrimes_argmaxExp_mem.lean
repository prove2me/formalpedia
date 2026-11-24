-- Prove2me | Theorems.Thm_DeletedPrimes_argmaxExp_mem
-- name    : DeletedPrimes.argmaxExp_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:54:17.81581+00:00
-- url     : https://prove2.me/theorems/a7ac1771-b709-47e8-a77a-dfa29ca0efe9
-- title:
--   Deleted Primes: argmax Exp mem
-- statement:
--   The Deleted Primes construction uses the argmax Exp mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L206-L220
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L206-L220

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.argmaxExp_mem {k : ℕ} (hk : 1 ≤ k) {α κ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hκ : 0 ≤ κ) :
    argmaxExp k α κ ∈ Set.Icc 0 κ := by sorry
