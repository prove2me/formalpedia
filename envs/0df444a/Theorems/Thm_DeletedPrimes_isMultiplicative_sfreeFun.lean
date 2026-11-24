-- Prove2me | Theorems.Thm_DeletedPrimes_isMultiplicative_sfreeFun
-- name    : DeletedPrimes.isMultiplicative_sfreeFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:51:20.739264+00:00
-- url     : https://prove2.me/theorems/ec343679-be22-4391-89bd-d818aa6e5386
-- title:
--   Deleted Primes: is Multiplicative sfree Fun
-- statement:
--   The Deleted Primes construction uses the is Multiplicative sfree Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L105-L114
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L105-L114

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.isMultiplicative_sfreeFun (hS : ∀ p ∈ S, p.Prime) : (sfreeFun S).IsMultiplicative := by sorry
