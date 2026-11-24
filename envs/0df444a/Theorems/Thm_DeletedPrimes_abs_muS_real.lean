-- Prove2me | Theorems.Thm_DeletedPrimes_abs_muS_real
-- name    : DeletedPrimes.abs_muS_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:51:05.116692+00:00
-- url     : https://prove2.me/theorems/f4c75966-1157-49b8-b184-5139cca34191
-- title:
--   Deleted Primes: abs mu S real
-- statement:
--   The Deleted Primes construction uses the abs mu S real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L56-L62
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L56-L62

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.abs_muS_real (d : ℕ) : |(muS S d : ℝ)| = if muS S d = 0 then 0 else 1 := by sorry
