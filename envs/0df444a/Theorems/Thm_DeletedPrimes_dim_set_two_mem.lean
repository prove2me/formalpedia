-- Prove2me | Theorems.Thm_DeletedPrimes_dim_set_two_mem
-- name    : DeletedPrimes.dim_set_two_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:48:31.968527+00:00
-- url     : https://prove2.me/theorems/8339b298-4530-45c7-b304-7254a696156e
-- title:
--   Deleted Primes: dim set two mem
-- statement:
--   The Deleted Primes construction uses the dim set two mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L251-L253
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L251-L253

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.dim_set_two_mem (S : Set ℕ) :
    (2 : ℝ) ∈ {σ : ℝ | 0 ≤ σ ∧ Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-σ))} := by sorry
