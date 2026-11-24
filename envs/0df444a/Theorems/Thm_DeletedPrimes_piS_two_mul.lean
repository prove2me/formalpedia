-- Prove2me | Theorems.Thm_DeletedPrimes_piS_two_mul
-- name    : DeletedPrimes.piS_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:57:34.327428+00:00
-- url     : https://prove2.me/theorems/511890b6-0a7d-43c1-b9d9-c389682ce081
-- title:
--   Deleted Primes: pi S two mul
-- statement:
--   `π_S(2X) = π_S(X) + #(S ∩ (X, 2X])` for `X ≥ 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Smooth.lean#L33-L45
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Smooth.lean#L33-L45

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Smooth
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.piS_two_mul {S : Set ℕ} {X : ℝ} (hX : 1 ≤ X) :
    piS S (2 * X) = piS S X + intervalCount S X := by sorry
