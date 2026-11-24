-- Prove2me | Theorems.Thm_DeletedPrimes_share_bound
-- name    : DeletedPrimes.share_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:57:48.45416+00:00
-- url     : https://prove2.me/theorems/8a4bc2eb-a708-43ad-b449-eb72dd9dbcfe
-- title:
--   Deleted Primes: share bound
-- statement:
--   The block shares: if `L/k ≤ ℓ_i ≤ (1+w) L/k` for all `i`, then `|ℓ_i / ∑ ℓ − 1/k| ≤ w/k`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L71-L101
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L71-L101

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.share_bound {k : ℕ} (hk : 1 ≤ k) {L w : ℝ} (hL : 0 < L) (ℓ : Fin k → ℝ)
    (hℓ : ∀ i, L / k ≤ ℓ i ∧ ℓ i ≤ (1 + w) * L / k) (i : Fin k) :
    L ≤ ∑ i', ℓ i' ∧ |ℓ i / ∑ i', ℓ i' - 1 / k| ≤ w / k := by sorry
