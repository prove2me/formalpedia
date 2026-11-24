-- Prove2me | Theorems.Thm_DeletedPrimes_primeCount_ge
-- name    : DeletedPrimes.primeCount_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:08:47.750039+00:00
-- url     : https://prove2.me/theorems/e2b8843c-0f83-451e-979e-a25c50beb979
-- title:
--   Deleted Primes: prime Count ge
-- statement:
--   Proposition 4.1(3): `π_S(x) ≥ x^{α−ε}` for every large `x`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L301-L364
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L301-L364

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.primeCount_ge {S : Set ℕ} {α m : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hM : MertensLaw S α m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, x ^ (α - ε) ≤ primeCount S x := by sorry
