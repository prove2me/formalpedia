-- Prove2me | Theorems.Thm_DeletedPrimes_hyperbola_y_mem
-- name    : DeletedPrimes.hyperbola_y_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:10:37.712386+00:00
-- url     : https://prove2.me/theorems/2ab8f60d-4629-407c-899d-84a667d759d7
-- title:
--   Deleted Primes: hyperbola y mem
-- statement:
--   The hyperbola parameter `y = x^{β/(1+β−γ)}` lies in `[1, x]` for `x ≥ 1`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L162-L167
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/RandomDeletions.lean#L162-L167

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.hyperbola_y_mem {β γ x : ℝ} (hγ0 : 0 ≤ γ) (hγβ : γ < β) (hβ1 : β ≤ 1) (hx : 1 ≤ x) :
    1 ≤ x ^ (β / (1 + β - γ)) ∧ x ^ (β / (1 + β - γ)) ≤ x := by sorry
