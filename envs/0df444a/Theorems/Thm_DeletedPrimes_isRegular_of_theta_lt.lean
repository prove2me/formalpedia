-- Prove2me | Theorems.Thm_DeletedPrimes_isRegular_of_theta_lt
-- name    : DeletedPrimes.isRegular_of_theta_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:47:39.058723+00:00
-- url     : https://prove2.me/theorems/7fb3533b-40cf-4ae0-949e-9223dcc43aaf
-- title:
--   Deleted Primes: is Regular of theta lt
-- statement:
--   Every exponent above `θ(S)` is admissible.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L171-L173
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L171-L173

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.isRegular_of_theta_lt {S : Set ℕ} {θ : ℝ} (h : theta S < θ) : IsRegular S θ := by sorry
