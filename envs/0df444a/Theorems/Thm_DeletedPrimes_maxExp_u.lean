-- Prove2me | Theorems.Thm_DeletedPrimes_maxExp_u
-- name    : DeletedPrimes.maxExp_u
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T21:48:36.627195+00:00
-- url     : https://prove2.me/theorems/e6c679a6-9687-49ec-b80b-52ee4a2bd103
-- title:
--   Deleted Primes: max Exp u
-- statement:
--   The Deleted Primes construction uses the max Exp u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L117-L128
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L117-L128

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.maxExp_u {k : ℕ} (hk : 1 ≤ k) (α u : ℝ) :
    maxExp k α (k * u) = if α ≤ 1 / 2 then (α - 1) + 2 * (k * u) - 2 * α * (k * u) + α ^ 2 * u
      else (α - 1) + k * u + (1 - α) ^ 2 * u := by sorry
