-- Prove2me | Theorems.Thm_DeletedPrimes_le_of_forall_small
-- name    : DeletedPrimes.le_of_forall_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:57:41.43387+00:00
-- url     : https://prove2.me/theorems/297fe4ac-9505-4864-afac-602094a9ccc1
-- title:
--   Deleted Primes: le of forall small
-- statement:
--   If `κ(α − η) ≤ B` for every `η ∈ (0, η₀)`, then `κα ≤ B`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L56-L68
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L56-L68

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.le_of_forall_small {κ α B η₀ : ℝ} (hκ : 0 < κ) (hη₀ : 0 < η₀)
    (h : ∀ η : ℝ, 0 < η → η < η₀ → κ * (α - η) ≤ B) : κ * α ≤ B := by sorry
