-- Prove2me | Theorems.Thm_DeletedPrimes_cross_terms_cancel
-- name    : DeletedPrimes.cross_terms_cancel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:10:31.106915+00:00
-- url     : https://prove2.me/theorems/2e0626c2-1080-418e-b547-b4bea754f16d
-- title:
--   Deleted Primes: cross terms cancel
-- statement:
--   The three cross terms in `a x^β y^{1−β}` cancel: `1/(1−β) − β/(1−β) − 1 = 0`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L179-L182
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L179-L182

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.cross_terms_cancel {a β : ℝ} (hβ : β ≠ 1) : a / (1 - β) - a * β / (1 - β) - a = 0 := by sorry
