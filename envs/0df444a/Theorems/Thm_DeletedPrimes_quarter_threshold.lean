-- Prove2me | Theorems.Thm_DeletedPrimes_quarter_threshold
-- name    : DeletedPrimes.quarter_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:09:56.813334+00:00
-- url     : https://prove2.me/theorems/908ae4f8-d514-4b24-b7fb-f1e9e537a4ae
-- title:
--   Deleted Primes: quarter threshold
-- statement:
--   **Corollary 4.** For every `θ > 1/4` some deletion is `θ`-regular and its zeta function has a zero with real part
--   `> 1/2` (`ZeroRight S`). If RH fails, `S = ∅` works (`hnotRH`); if RH holds, the random deletions of Corollary 3 with
--   `1/2 < α < 2θ` work (`hRH`).
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L126-L139
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L126-L139

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.quarter_threshold (ZeroRight : Set ℕ → Prop)
    (hnotRH : ¬ RiemannHypothesis → ZeroRight ∅)
    (hRH : RiemannHypothesis → ∀ α : ℝ, 1 / 2 < α → α < 1 → ∃ S : Set ℕ, theta S = α / 2 ∧ ZeroRight S) :
    ∀ θ : ℝ, 1 / 4 < θ → ∃ S : Set ℕ, IsRegular S θ ∧ ZeroRight S := by sorry
