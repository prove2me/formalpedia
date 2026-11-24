-- Prove2me | Theorems.Thm_DeletedPrimes_isRegular_empty
-- name    : DeletedPrimes.isRegular_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:57:21.676594+00:00
-- url     : https://prove2.me/theorems/85c90c89-5da8-44c4-a372-c705761adb66
-- title:
--   Deleted Primes: is Regular empty
-- statement:
--   The empty deletion: `N_∅(x) = ⌊x⌋` and `a_∅ = 1`, so `|E(x)| ≤ 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L112-L121
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L112-L121

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.isRegular_empty {θ : ℝ} (hθ : 0 ≤ θ) : IsRegular ∅ θ := by sorry
