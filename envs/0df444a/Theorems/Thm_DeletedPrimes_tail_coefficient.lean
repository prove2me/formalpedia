-- Prove2me | Theorems.Thm_DeletedPrimes_tail_coefficient
-- name    : DeletedPrimes.tail_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:11:59.23609+00:00
-- url     : https://prove2.me/theorems/c73baa32-2b8c-433e-9673-a3cfbee84cee
-- title:
--   Deleted Primes: tail coefficient
-- statement:
--   The tail of `ζ(1/β)`: `1/(1/β − 1) = β/(1−β)`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L194-L196
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L194-L196

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.tail_coefficient {β : ℝ} (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) : 1 / (1 / β - 1) = β / (1 - β) := by sorry
