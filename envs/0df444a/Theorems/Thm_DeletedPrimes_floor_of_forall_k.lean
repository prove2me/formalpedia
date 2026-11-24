-- Prove2me | Theorems.Thm_DeletedPrimes_floor_of_forall_k
-- name    : DeletedPrimes.floor_of_forall_k
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:54:33.468113+00:00
-- url     : https://prove2.me/theorems/4b35661f-5e73-488b-8543-c0994779012c
-- title:
--   Deleted Primes: floor of forall k
-- statement:
--   If `ακ_k(α) ≤ 2θ` for every `k ≥ 1`, then `(α/2) min(1/2, 1−α) ≤ θ`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L408-L413
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L408-L413

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.floor_of_forall_k {α θ : ℝ} (h1 : α < 1)
    (h : ∀ k : ℕ, 1 ≤ k → α * kappaK k α ≤ 2 * θ) : α / 2 * min (1 / 2) (1 - α) ≤ θ := by sorry
