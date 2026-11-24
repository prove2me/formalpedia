-- Prove2me | Theorems.Thm_DeletedPrimes_mertensSum_sub
-- name    : DeletedPrimes.mertensSum_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:49:23.370801+00:00
-- url     : https://prove2.me/theorems/31ff3e0b-65de-49bb-9677-77a891c963bf
-- title:
--   Deleted Primes: mertens Sum sub
-- statement:
--   The Deleted Primes construction uses the mertens Sum sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L110-L120
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L110-L120

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.mertensSum_sub (S : Set ℕ) (α : ℝ) {a b : ℝ} (hab : a ≤ b) :
    mertensSum S α b - mertensSum S α a =
      ∑ p ∈ (Finset.Icc 1 ⌊b⌋₊).filter (· ∈ S) \ (Finset.Icc 1 ⌊a⌋₊).filter (· ∈ S),
        Real.log p / (p : ℝ) ^ α := by sorry
