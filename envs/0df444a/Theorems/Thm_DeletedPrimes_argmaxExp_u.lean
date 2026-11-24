-- Prove2me | Theorems.Thm_DeletedPrimes_argmaxExp_u
-- name    : DeletedPrimes.argmaxExp_u
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:53:43.328792+00:00
-- url     : https://prove2.me/theorems/73dc075a-bd36-4cc5-82f6-fa18182ba8a1
-- title:
--   Deleted Primes: argmax Exp u
-- statement:
--   The Deleted Primes construction uses the argmax Exp u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L130-L136
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L130-L136

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.argmaxExp_u {k : ℕ} (hk : 1 ≤ k) (α u : ℝ) :
    argmaxExp k α (k * u) = if α ≤ 1 / 2 then k * u - α * u else (1 - α) * u := by sorry
