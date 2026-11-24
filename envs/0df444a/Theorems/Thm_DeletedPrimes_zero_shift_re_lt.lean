-- Prove2me | Theorems.Thm_DeletedPrimes_zero_shift_re_lt
-- name    : DeletedPrimes.zero_shift_re_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:11:54.7738+00:00
-- url     : https://prove2.me/theorems/ebb46838-2b15-4106-8aba-708b3140c6ad
-- title:
--   Deleted Primes: zero shift re lt
-- statement:
--   Under RH a zero `ρ` of `ζ` has `Re ρ ≤ 1/2`; the corresponding zero `s = ρ − 1 + α` of `ζ(s+1−α)` has
--   `Re s < α/2` when `α < 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L228-L232
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L228-L232

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.zero_shift_re_lt {α : ℝ} {s ρ : ℂ} (hα1 : α < 1) (hρ : ρ.re ≤ 1 / 2) (h : s + 1 - α = ρ) :
    s.re < α / 2 := by sorry
