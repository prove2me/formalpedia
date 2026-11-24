-- Prove2me | Theorems.Thm_DeletedPrimes_band_contains_BDR
-- name    : DeletedPrimes.band_contains_BDR
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:12:32.857605+00:00
-- url     : https://prove2.me/theorems/79233401-f1c0-4c54-96cf-1572348320c9
-- title:
--   Deleted Primes: band contains BDR
-- statement:
--   The band contains the region of [BDR]: `α/2 < 2α/(α+2)` for `0 < α < 2`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L254-L256
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L254-L256

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.band_contains_BDR {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2) : α / 2 < 2 * α / (α + 2) := by sorry
