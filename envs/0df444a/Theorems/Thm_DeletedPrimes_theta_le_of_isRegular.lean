-- Prove2me | Theorems.Thm_DeletedPrimes_theta_le_of_isRegular
-- name    : DeletedPrimes.theta_le_of_isRegular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:47:30.13628+00:00
-- url     : https://prove2.me/theorems/a0dea7f1-0858-4c81-9b60-f4dc6af21e4f
-- title:
--   Deleted Primes: theta le of is Regular
-- statement:
--   An admissible exponent bounds `θ(S)`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L176-L177
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L176-L177

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.theta_le_of_isRegular {S : Set ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h : IsRegular S θ) : theta S ≤ θ := by sorry
