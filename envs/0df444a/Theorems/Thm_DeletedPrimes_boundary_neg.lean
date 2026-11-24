-- Prove2me | Theorems.Thm_DeletedPrimes_boundary_neg
-- name    : DeletedPrimes.boundary_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:04:04.027954+00:00
-- url     : https://prove2.me/theorems/61ecca25-64d9-44c0-9e5f-618eb3ee0252
-- title:
--   Deleted Primes: boundary neg
-- statement:
--   The term `+1` of Lemma 5.2, on `τ ∈ (κ, κ+ε]`: its exponent `(1−α)(2κ−1)` is negative for `κ < 1/2`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L339-L340
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L339-L340

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.boundary_neg {α κ : ℝ} (h1 : α < 1) (hκ : κ < 1 / 2) : (1 - α) * (2 * κ - 1) < 0 := by sorry
