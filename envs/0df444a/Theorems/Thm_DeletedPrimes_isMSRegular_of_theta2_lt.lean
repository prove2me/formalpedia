-- Prove2me | Theorems.Thm_DeletedPrimes_isMSRegular_of_theta2_lt
-- name    : DeletedPrimes.isMSRegular_of_theta2_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:50:40.427658+00:00
-- url     : https://prove2.me/theorems/cfd42b0c-fef3-4480-b3c9-1371aefaad4f
-- title:
--   Deleted Primes: is MSRegular of theta2 lt
-- statement:
--   Every exponent above `θ₂(S)` is admissible in mean square.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L246-L248
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Basic.lean#L246-L248

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.isMSRegular_of_theta2_lt {S : Set ℕ} {θ : ℝ} (h : theta2 S < θ) : IsMSRegular S θ := by sorry
