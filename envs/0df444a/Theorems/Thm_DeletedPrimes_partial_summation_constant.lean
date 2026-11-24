-- Prove2me | Theorems.Thm_DeletedPrimes_partial_summation_constant
-- name    : DeletedPrimes.partial_summation_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:11:35.291801+00:00
-- url     : https://prove2.me/theorems/faeb0218-558f-4ef7-bb73-333138d3ffc5
-- title:
--   Deleted Primes: partial summation constant
-- statement:
--   Partial summation: with `Y = y^{1−β}`, `a Y + aβ(Y − 1)/(1−β) = a Y/(1−β) + aβ/(β−1)`; the constant
--   `aβ/(β−1)` is the first term of `ζ_S(β)` in (2.1).
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L186-L191
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L186-L191

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.partial_summation_constant {a β Y : ℝ} (hβ : β ≠ 1) :
    a * Y + a * β * (Y - 1) / (1 - β) = a * Y / (1 - β) + a * β / (β - 1) := by sorry
