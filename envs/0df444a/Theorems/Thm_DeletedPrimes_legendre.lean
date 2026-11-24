-- Prove2me | Theorems.Thm_DeletedPrimes_legendre
-- name    : DeletedPrimes.legendre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:10.930663+00:00
-- url     : https://prove2.me/theorems/a3b4ea17-2139-441b-adea-7d3cbd6ab10c
-- title:
--   Deleted Primes: legendre
-- statement:
--   Legendre's identity (5.1):
--   `E(x) = −∑_{d≤x} μ_S(d) b(x/d) − M_S(x)/2 − x ∑_{d>x} μ_S(d)/d`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L421-L436
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L421-L436

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.legendre (hS : ∀ p ∈ S, p.Prime) (hsum : Summable fun d : ℕ => (muS S d : ℝ) / d)
    {x : ℝ} (hx : 1 ≤ x) :
    err S x = -(∑ d ∈ Finset.Icc 1 ⌊x⌋₊, (muS S d : ℝ) * saw (x / d)) - mertensS S x / 2
      - x * ∑' d : ℕ, (if x < d then (muS S d : ℝ) / d else 0) := by sorry
