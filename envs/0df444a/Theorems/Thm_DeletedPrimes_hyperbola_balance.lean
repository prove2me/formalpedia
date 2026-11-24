-- Prove2me | Theorems.Thm_DeletedPrimes_hyperbola_balance
-- name    : DeletedPrimes.hyperbola_balance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:10:32.66539+00:00
-- url     : https://prove2.me/theorems/21583c5e-67ea-40eb-8563-76609d7357ea
-- title:
--   Deleted Primes: hyperbola balance
-- statement:
--   At `y = x^{β/(1+β−γ)}` the two error terms `x^β y^{γ−β}` and `y` coincide.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L170-L176
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L170-L176

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.hyperbola_balance {β γ x : ℝ} (hx : 0 < x) (hγβ : γ < β) :
    x ^ β * (x ^ (β / (1 + β - γ))) ^ (γ - β) = x ^ (β / (1 + β - γ)) := by sorry
