-- Prove2me | Theorems.Thm_DeletedPrimes_kappaK_one
-- name    : DeletedPrimes.kappaK_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:48:43.772575+00:00
-- url     : https://prove2.me/theorems/88b2964d-49aa-47f4-8525-39468cb12944
-- title:
--   Deleted Primes: kappa K one
-- statement:
--   The Deleted Primes construction uses the kappa K one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L138-L142
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L138-L142

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.kappaK_one (α : ℝ) : kappaK 1 α = kappaOne α := by sorry
