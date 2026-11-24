-- Prove2me | Theorems.Thm_DeletedPrimes_floor_theta
-- name    : DeletedPrimes.floor_theta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:13:59.973309+00:00
-- url     : https://prove2.me/theorems/e38557f8-c295-4d45-b1a8-d2bcfa81de6b
-- title:
--   Deleted Primes: floor theta
-- statement:
--   **Theorem 6(3)**: `θ(S) ≥ θ₂(S) ≥ (α/2) min(1/2, 1−α)`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L368-L370
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L368-L370

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.floor_theta {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) (Q : Quantization S) : dim S / 2 * min (1 / 2) (1 - dim S) ≤ theta S := by sorry
