-- Prove2me | Theorems.Thm_DeletedPrimes_composite_floor
-- name    : DeletedPrimes.composite_floor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:58:01.0068+00:00
-- url     : https://prove2.me/theorems/b9e39d57-c83e-420f-ac38-852146b20728
-- title:
--   Deleted Primes: composite floor
-- statement:
--   **Theorem 6(2).** `α κ_k(α) ≤ 2θ₂(S)` for every `k ≥ 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L329-L358
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L329-L358

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.composite_floor {S : Set ℕ} (hα0 : 0 < dim S) (hα1 : dim S < 1)
    (F : Frame S) (Q : Quantization S) {k : ℕ} (hk : 1 ≤ k) :
    dim S * kappaK k (dim S) ≤ 2 * theta2 S := by sorry
