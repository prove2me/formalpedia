-- Prove2me | Theorems.Thm_DeletedPrimes_kappaK_pos
-- name    : DeletedPrimes.kappaK_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:48:44.529151+00:00
-- url     : https://prove2.me/theorems/ad7f8589-ddea-46ec-b061-db65cfc3055f
-- title:
--   Deleted Primes: kappa K pos
-- statement:
--   The Deleted Primes construction uses the kappa K pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L172-L179
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Exponents.lean#L172-L179

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section

theorem DeletedPrimes.kappaK_pos {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) : 0 < kappaK k α := by sorry
