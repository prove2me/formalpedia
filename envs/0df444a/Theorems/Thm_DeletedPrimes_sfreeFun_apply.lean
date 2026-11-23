-- Prove2me | Theorems.Thm_DeletedPrimes_sfreeFun_apply
-- name    : DeletedPrimes.sfreeFun_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:45:59.256499+00:00
-- url     : https://prove2.me/theorems/5638f60b-e481-48a5-8b0e-b0821e6a5288
-- title:
--   Deleted Primes: sfree Fun apply
-- statement:
--   The Deleted Primes construction uses the sfree Fun apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L92-L92
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L92-L92

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.sfreeFun_apply (n : ℕ) : sfreeFun S n = if n ≠ 0 ∧ SFree S n then 1 else 0 := by sorry
