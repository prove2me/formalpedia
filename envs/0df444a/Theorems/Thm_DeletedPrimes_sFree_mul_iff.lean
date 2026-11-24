-- Prove2me | Theorems.Thm_DeletedPrimes_sFree_mul_iff
-- name    : DeletedPrimes.sFree_mul_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:51:18.084995+00:00
-- url     : https://prove2.me/theorems/b37222df-28ee-4f3d-afe3-5fe4e042d053
-- title:
--   Deleted Primes: s Free mul iff
-- statement:
--   The Deleted Primes construction uses the s Free mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L94-L103
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L94-L103

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.sFree_mul_iff (hS : ∀ p ∈ S, p.Prime) {m n : ℕ} :
    SFree S (m * n) ↔ SFree S m ∧ SFree S n := by sorry
