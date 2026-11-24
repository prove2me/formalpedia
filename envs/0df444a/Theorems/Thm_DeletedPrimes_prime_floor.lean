-- Prove2me | Theorems.Thm_DeletedPrimes_prime_floor
-- name    : DeletedPrimes.prime_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:13:57.434173+00:00
-- url     : https://prove2.me/theorems/20389b15-7523-492d-af82-4291b475a9ad
-- title:
--   Deleted Primes: prime floor
-- statement:
--   The prime floor: `α κ_1(α) ≤ 2θ₂(S)`, hence `θ(S) ≥ θ₂(S) ≥ α(1−α)/(2(1+(1−α)²))`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L182-L207
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L182-L207

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.prime_floor {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) : dim S * kappaOne (dim S) ≤ 2 * theta2 S := by sorry
