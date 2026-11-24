-- Prove2me | Theorems.Thm_DeletedPrimes_hyperbola_exponent_mem
-- name    : DeletedPrimes.hyperbola_exponent_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:57:44.256325+00:00
-- url     : https://prove2.me/theorems/af97152a-b856-48ed-b0a8-37107b742823
-- title:
--   Deleted Primes: hyperbola exponent mem
-- statement:
--   `0 < β/(1+β−γ) ≤ 1` for `0 ≤ γ < β ≤ 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L154-L159
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L154-L159

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.hyperbola_exponent_mem {β γ : ℝ} (hγ0 : 0 ≤ γ) (hγβ : γ < β) (hβ1 : β ≤ 1) :
    0 < β / (1 + β - γ) ∧ β / (1 + β - γ) ≤ 1 := by sorry
