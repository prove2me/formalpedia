-- Prove2me | Theorems.Thm_DeletedPrimes_pole_mem_halfplane
-- name    : DeletedPrimes.pole_mem_halfplane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:12:18.527896+00:00
-- url     : https://prove2.me/theorems/d3379103-e2f8-4f8f-bcd0-127a16ccb6e6
-- title:
--   Deleted Primes: pole mem halfplane
-- statement:
--   The pole `s = α` of `ζ(s+1−α)` lies in `Re s > α/2` when `α > 0`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L243-L243
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L243-L243

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.pole_mem_halfplane {α : ℝ} (hα0 : 0 < α) : α / 2 < α := by sorry
