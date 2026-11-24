-- Prove2me | Theorems.Thm_DeletedPrimes_muSFun_mul_zeta
-- name    : DeletedPrimes.muSFun_mul_zeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:48:10.970055+00:00
-- url     : https://prove2.me/theorems/7b6c57b2-2ceb-4e66-9cce-b9dfa11aca00
-- title:
--   Deleted Primes: mu SFun mul zeta
-- statement:
--   The Deleted Primes construction uses the mu SFun mul zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L122-L144
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L122-L144

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.muSFun_mul_zeta (hS : ∀ p ∈ S, p.Prime) :
    muSFun S * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) = sfreeFun S := by sorry
