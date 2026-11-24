-- Prove2me | Theorems.Thm_DeletedPrimes_split_balance
-- name    : DeletedPrimes.split_balance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:09:18.278807+00:00
-- url     : https://prove2.me/theorems/57fa5186-7cb0-4497-90a7-02ef69f9dbe2
-- title:
--   Deleted Primes: split balance
-- statement:
--   Proposition 7.3, step 4: with `K = y^{1/2}`, `K^α = y^{1/2} K^{α−1} = y^{α/2}`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L41-L45
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L41-L45

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.split_balance {y α : ℝ} (hy : 0 < y) :
    (y ^ (1 / 2 : ℝ)) ^ α = y ^ (α / 2) ∧ y ^ (1 / 2 : ℝ) * (y ^ (1 / 2 : ℝ)) ^ (α - 1) = y ^ (α / 2) := by sorry
