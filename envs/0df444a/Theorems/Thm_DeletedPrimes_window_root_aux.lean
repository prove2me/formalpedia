-- Prove2me | Theorems.Thm_DeletedPrimes_window_root_aux
-- name    : DeletedPrimes.window_root_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:49:07.648824+00:00
-- url     : https://prove2.me/theorems/e431237d-a406-4b82-bff8-26b202fd6f2d
-- title:
--   Deleted Primes: window root aux
-- statement:
--   Auxiliary version of `window_root` (stated before its use in `counterexample_window`).
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L421-L431
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L421-L431

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.window_root_aux {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ8 : θ < 1 / 8) :
    (1 - Real.sqrt (1 - 8 * θ)) / 2 * (1 - (1 - Real.sqrt (1 - 8 * θ)) / 2) = 2 * θ ∧
      0 ≤ (1 - Real.sqrt (1 - 8 * θ)) / 2 ∧ (1 - Real.sqrt (1 - 8 * θ)) / 2 < 1 / 2 := by sorry
