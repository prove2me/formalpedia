-- Prove2me | Theorems.Thm_DeletedPrimes_window_root
-- name    : DeletedPrimes.window_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:05:49.357321+00:00
-- url     : https://prove2.me/theorems/c29487ec-3a17-4cf2-b9d3-43224dd07cd0
-- title:
--   Deleted Primes: window root
-- statement:
--   `u(θ) = (1 − √(1−8θ))/2` is the root in `[0, 1/2)` of `u(1−u) = 2θ`, for `0 ≤ θ < 1/8`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L453-L456
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L453-L456

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.window_root {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ8 : θ < 1 / 8) :
    let u := (1 - Real.sqrt (1 - 8 * θ)) / 2
    u * (1 - u) = 2 * θ ∧ 0 ≤ u ∧ u < 1 / 2 := by sorry
