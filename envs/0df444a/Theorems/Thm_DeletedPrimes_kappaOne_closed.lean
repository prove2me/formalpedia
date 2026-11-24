-- Prove2me | Theorems.Thm_DeletedPrimes_kappaOne_closed
-- name    : DeletedPrimes.kappaOne_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:05:04.535726+00:00
-- url     : https://prove2.me/theorems/b6432409-eefe-46dd-a7cb-94e786b21b5b
-- title:
--   Deleted Primes: kappa One closed
-- statement:
--   The Deleted Primes construction uses the kappa One closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L415-L418
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L415-L418

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.kappaOne_closed (α : ℝ) : α * kappaOne α / 2 = α * (1 - α) / (2 * (1 + (1 - α) ^ 2)) := by sorry
