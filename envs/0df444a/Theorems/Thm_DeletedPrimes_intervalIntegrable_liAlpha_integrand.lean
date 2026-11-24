-- Prove2me | Theorems.Thm_DeletedPrimes_intervalIntegrable_liAlpha_integrand
-- name    : DeletedPrimes.intervalIntegrable_liAlpha_integrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:57:36.151688+00:00
-- url     : https://prove2.me/theorems/c8326aef-cff5-4120-9fcc-66413649c055
-- title:
--   Deleted Primes: interval Integrable li Alpha integrand
-- statement:
--   The integrand of `li_α` is interval integrable on `[a, b] ⊆ [2, ∞)`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Smooth.lean#L48-L57
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Smooth.lean#L48-L57

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Smooth
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.intervalIntegrable_liAlpha_integrand (α : ℝ) {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun u : ℝ => u ^ (α - 1) / Real.log u) MeasureTheory.volume a b := by sorry
