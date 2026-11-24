-- Prove2me | Theorems.Thm_DeletedPrimes_counterexample_window
-- name    : DeletedPrimes.counterexample_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:54:54.809455+00:00
-- url     : https://prove2.me/theorems/b3abaa9b-f133-4083-a2ec-5d58c63c3fe6
-- title:
--   Deleted Primes: counterexample window
-- statement:
--   Corollary 7 (counterexample window): for `θ < 1/8`, a deletion with `θ < α/2` that obeys the floor has
--   `α ∈ (2θ, 4θ] ∪ [1 − u(θ), 1)`, `u(θ) = (1 − √(1−8θ))/2`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L435-L450
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L435-L450

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.counterexample_window {α θ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hθ8 : θ < 1 / 8)
    (hθα : θ < α / 2) (hfloor : α / 2 * min (1 / 2) (1 - α) ≤ θ) :
    (2 * θ < α ∧ α ≤ 4 * θ) ∨ 1 - (1 - Real.sqrt (1 - 8 * θ)) / 2 ≤ α := by sorry
