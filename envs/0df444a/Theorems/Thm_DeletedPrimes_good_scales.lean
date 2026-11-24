-- Prove2me | Theorems.Thm_DeletedPrimes_good_scales
-- name    : DeletedPrimes.good_scales
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:56:48.32504+00:00
-- url     : https://prove2.me/theorems/92f9c4ad-dc5a-4e4d-abcd-e040f73b632c
-- title:
--   Deleted Primes: good scales
-- statement:
--   `k` dense dyadic blocks at once, near the scales `X^{λ_i}`, strictly increasing when the `λ_i` are separated:
--   `λ_i (1+δ) < λ_{i'}` for `i < i'`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L274-L298
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/GoodScales.lean#L274-L298

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_GoodScales
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.good_scales {S : Set ℕ} {α m : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hM : MertensLaw S α m) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) {k : ℕ} (lam : Fin k → ℝ)
    (hlam : ∀ i, 0 < lam i) (hsep : ∀ i i' : Fin k, i < i' → lam i * (1 + δ) < lam i') :
    ∀ᶠ X : ℝ in atTop, ∃ j : Fin k → ℕ, StrictMono j ∧ ∀ i,
      X ^ lam i ≤ 2 ^ j i ∧ (2 : ℝ) ^ j i ≤ X ^ (lam i * (1 + δ)) ∧
      ((2 : ℝ) ^ j i) ^ (α - ε) ≤ blockCount S (2 ^ j i) := by sorry
