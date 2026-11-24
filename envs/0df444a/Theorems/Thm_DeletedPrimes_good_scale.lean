-- Prove2me | Theorems.Thm_DeletedPrimes_good_scale
-- name    : DeletedPrimes.good_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:56:58.025821+00:00
-- url     : https://prove2.me/theorems/80bd3884-a5c5-4224-8ffe-e8ac56c0c5d3
-- title:
--   Deleted Primes: good scale
-- statement:
--   Proposition 4.1(1): a dense dyadic block in every polynomial range `[X, X^{1+δ}]`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L177-L270
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L177-L270

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.good_scale {S : Set ℕ} {α m : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hM : MertensLaw S α m) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∃ j : ℕ, X ≤ 2 ^ j ∧ (2 : ℝ) ^ j ≤ X ^ (1 + δ) ∧
      ((2 : ℝ) ^ j) ^ (α - ε) ≤ blockCount S (2 ^ j) := by sorry
