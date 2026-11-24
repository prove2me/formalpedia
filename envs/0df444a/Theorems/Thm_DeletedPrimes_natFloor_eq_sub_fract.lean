-- Prove2me | Theorems.Thm_DeletedPrimes_natFloor_eq_sub_fract
-- name    : DeletedPrimes.natFloor_eq_sub_fract
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:52:46.892124+00:00
-- url     : https://prove2.me/theorems/85c06433-c0e9-4b21-a23a-c25558a5cc72
-- title:
--   Deleted Primes: nat Floor eq sub fract
-- statement:
--   The Deleted Primes construction uses the nat Floor eq sub fract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L370-L371
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Legendre.lean#L370-L371

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}

theorem DeletedPrimes.natFloor_eq_sub_fract {u : ℝ} (hu : 0 ≤ u) : (⌊u⌋₊ : ℝ) = u - Int.fract u := by sorry
