-- Prove2me | Theorems.Thm_DeletedPrimes_le_two_theta2_of_frequently
-- name    : DeletedPrimes.le_two_theta2_of_frequently
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:49:45.770887+00:00
-- url     : https://prove2.me/theorems/4a39b0c1-73ae-4b68-b146-6bd517607ebc
-- title:
--   Deleted Primes: le two theta2 of frequently
-- statement:
--   A mean-square lower bound along arbitrarily large `X` bounds `θ₂` from below.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L168-L179
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L168-L179

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.le_two_theta2_of_frequently {S : Set ℕ} {a c : ℝ} (hc : 0 < c)
    (h : ∃ᶠ X : ℝ in atTop, c * X ^ a ≤ meanSq S X) : a ≤ 2 * theta2 S := by sorry
