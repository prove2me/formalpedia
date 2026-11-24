-- Prove2me | Theorems.Thm_DeletedPrimes_log_two_bounds
-- name    : DeletedPrimes.log_two_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:56:27.343122+00:00
-- url     : https://prove2.me/theorems/148c1ea9-1567-4dce-ae10-700d76be6b96
-- title:
--   Deleted Primes: log two bounds
-- statement:
--   The Deleted Primes construction uses the log two bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L160-L164
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L160-L164

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.log_two_bounds {p : ℕ} (hp : p ≠ 0) :
    2 ^ Nat.log 2 p ≤ p ∧ p < 2 * 2 ^ Nat.log 2 p := by sorry
