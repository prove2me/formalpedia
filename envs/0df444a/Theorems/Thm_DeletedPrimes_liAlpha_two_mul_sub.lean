-- Prove2me | Theorems.Thm_DeletedPrimes_liAlpha_two_mul_sub
-- name    : DeletedPrimes.liAlpha_two_mul_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:57:38.067807+00:00
-- url     : https://prove2.me/theorems/9020ff14-bdbe-4bdc-ae86-98394beb804e
-- title:
--   Deleted Primes: li Alpha two mul sub
-- statement:
--   `li_α(2X) − li_α(X) ≥ 2^{α−2} X^α / log X` for `X ≥ 2` and `α ≤ 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Smooth.lean#L60-L95
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Smooth.lean#L60-L95

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Smooth
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.liAlpha_two_mul_sub {α X : ℝ} (hα1 : α ≤ 1) (hX : 2 ≤ X) :
    2 ^ (α - 2) * X ^ α / Real.log X ≤ liAlpha α (2 * X) - liAlpha α X := by sorry
