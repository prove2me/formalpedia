-- Prove2me | Theorems.Thm_DeletedPrimes_hyperbola_tail_terms
-- name    : DeletedPrimes.hyperbola_tail_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:11:56.024065+00:00
-- url     : https://prove2.me/theorems/48052ef0-28ea-4224-9542-f514f610c2ab
-- title:
--   Deleted Primes: hyperbola tail terms
-- statement:
--   With `L = (x/y)^β`: `x L^{1−1/β} = x^β y^{1−β}`, `x L^{−1/β} = y`, `x^γ L^{1−γ/β} = x^β y^{γ−β}`,
--   `y L = x^β y^{1−β}` and `y^γ L = x^β y^{γ−β}`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L200-L224
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L200-L224

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.hyperbola_tail_terms {x y β γ : ℝ} (hx : 0 < x) (hy : 0 < y) (hβ : 0 < β) :
    x * ((x / y) ^ β) ^ (1 - 1 / β) = x ^ β * y ^ (1 - β) ∧
    x * ((x / y) ^ β) ^ (-(1 / β)) = y ∧
    x ^ γ * ((x / y) ^ β) ^ (1 - γ / β) = x ^ β * y ^ (γ - β) ∧
    y * (x / y) ^ β = x ^ β * y ^ (1 - β) ∧
    y ^ γ * (x / y) ^ β = x ^ β * y ^ (γ - β) := by sorry
