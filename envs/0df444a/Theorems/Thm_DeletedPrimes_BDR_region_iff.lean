-- Prove2me | Theorems.Thm_DeletedPrimes_BDR_region_iff
-- name    : DeletedPrimes.BDR_region_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:12:31.383963+00:00
-- url     : https://prove2.me/theorems/330ad1b8-7209-4c99-bb7a-ae79c5130dad
-- title:
--   Deleted Primes: BDR region iff
-- statement:
--   The region of [BDR] is nonempty, `2α/(α+2) < 1/2`, exactly when `α < 2/3`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L259-L261
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L259-L261

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.BDR_region_iff {α : ℝ} (hα0 : 0 < α) : 2 * α / (α + 2) < 1 / 2 ↔ α < 2 / 3 := by sorry
