-- Prove2me | Theorems.Thm_DeletedPrimes_band_nonempty
-- name    : DeletedPrimes.band_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:12:23.946787+00:00
-- url     : https://prove2.me/theorems/ee2300d8-13c1-41df-8f69-d8e9e48ef2f8
-- title:
--   Deleted Primes: band nonempty
-- statement:
--   The band `α/2 ≤ β < 1/2` is nonempty for `α < 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L251-L251
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L251-L251

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.band_nonempty {α : ℝ} (hα1 : α < 1) : α / 2 < 1 / 2 := by sorry
