-- Prove2me | Theorems.Thm_DeletedPrimes_counterexample_window_of_deletion
-- name    : DeletedPrimes.counterexample_window_of_deletion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:14:49.999811+00:00
-- url     : https://prove2.me/theorems/cf5284d3-8259-4bc8-8c5f-5e99bda5e013
-- title:
--   Deleted Primes: counterexample window of deletion
-- statement:
--   **Corollary 7** (the counterexample window).
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L376-L383
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/CompositeFloor.lean#L376-L383

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.counterexample_window_of_deletion {S : Set ℕ} (F : Frame S)
    (Q : Quantization S) (L : LandauAtOne S) {θ : ℝ} (hθ8 : θ < 1 / 8) (hθ2 : theta2 S ≤ θ)
    (hθα : θ < dim S / 2) :
    (2 * θ < dim S ∧ dim S ≤ 4 * θ) ∨ 1 - (1 - Real.sqrt (1 - 8 * θ)) / 2 ≤ dim S := by sorry
