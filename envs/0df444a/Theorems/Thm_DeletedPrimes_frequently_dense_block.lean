-- Prove2me | Theorems.Thm_DeletedPrimes_frequently_dense_block
-- name    : DeletedPrimes.frequently_dense_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:55:43.259818+00:00
-- url     : https://prove2.me/theorems/b0011881-5fd7-4e9c-a290-c68a1bbba738
-- title:
--   Deleted Primes: frequently dense block
-- statement:
--   (5.4): below the dimension, dense dyadic blocks occur infinitely often.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L43-L106
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L43-L106

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.frequently_dense_block {S : Set ℕ} {σ η : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : σ < dim S) (hη : 0 < η) :
    ∃ᶠ j : ℕ in atTop, ((2 : ℝ) ^ j) ^ (σ - η) ≤ blockCount S (2 ^ j) := by sorry
