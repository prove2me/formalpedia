-- Prove2me | Theorems.Thm_DeletedPrimes_errExp_le_maxExp
-- name    : DeletedPrimes.errExp_le_maxExp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:44:30.575529+00:00
-- url     : https://prove2.me/theorems/97bf68fe-2ae7-4246-9a51-42c17ede9e6a
-- title:
--   Deleted Primes: err Exp le max Exp
-- statement:
--   The Deleted Primes construction uses the err Exp le max Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L222-L268
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L222-L268

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.errExp_le_maxExp {k : ℕ} (hk : 1 ≤ k) {α κ τ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hκ : 0 ≤ κ)
    (hτ0 : 0 ≤ τ) (hτκ : τ ≤ κ) : errExp k α κ τ ≤ maxExp k α κ := by sorry
