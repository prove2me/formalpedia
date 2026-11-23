-- Prove2me | Theorems.Thm_DeletedPrimes_le_of_frequently_rpow_le
-- name    : DeletedPrimes.le_of_frequently_rpow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:45:50.991362+00:00
-- url     : https://prove2.me/theorems/0eeaf086-9415-4915-8c92-4628d5d48bbb
-- title:
--   Deleted Primes: le of frequently rpow le
-- statement:
--   If `c X^a ≤ C X^b` for arbitrarily large `X`, with `c > 0`, then `a ≤ b`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L263-L285
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L263-L285

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.le_of_frequently_rpow_le {a b c C : ℝ} (hc : 0 < c)
    (h : ∃ᶠ X in atTop, c * X ^ a ≤ C * X ^ b) : a ≤ b := by sorry
