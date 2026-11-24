-- Prove2me | Theorems.Thm_DeletedPrimes_abs_err_le_rankin
-- name    : DeletedPrimes.abs_err_le_rankin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:30.186438+00:00
-- url     : https://prove2.me/theorems/a5e1b088-0b48-4673-8a8a-c352c56c428e
-- title:
--   Deleted Primes: abs err le rankin
-- statement:
--   The trivial bound of §5.1: `|E(x)| ≤ 2K(σ) x^σ` for `x ≥ 1`, whenever `0 ≤ σ ≤ 1` and `K(σ) < ∞`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L439-L486
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L439-L486

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.abs_err_le_rankin (hS : ∀ p ∈ S, p.Prime) {σ : ℝ}
    (hsum : Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ)) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (h1 : Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-1 : ℝ))) {x : ℝ} (hx : 1 ≤ x) :
    |err S x| ≤ 2 * unitSum S σ * x ^ σ := by sorry
