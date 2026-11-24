-- Prove2me | Theorems.Thm_DeletedPrimes_hyperbola_exponent_lt
-- name    : DeletedPrimes.hyperbola_exponent_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:10:20.084532+00:00
-- url     : https://prove2.me/theorems/17119677-5e7b-4f0e-b137-7c2c1959a2ca
-- title:
--   Deleted Primes: hyperbola exponent lt
-- statement:
--   The hyperbola exponent `β/(1+β−γ)` is strictly below `β` when `0 < β` and `γ < β`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L148-L151
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L148-L151

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.hyperbola_exponent_lt {β γ : ℝ} (hβ : 0 < β) (hγβ : γ < β) : β / (1 + β - γ) < β := by sorry
