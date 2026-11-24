-- Prove2me | Theorems.Thm_DeletedPrimes_smooth_lower
-- name    : DeletedPrimes.smooth_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:13:01.518013+00:00
-- url     : https://prove2.me/theorems/6857238e-976c-43d8-8acf-fa61fd5fb349
-- title:
--   Deleted Primes: smooth lower
-- statement:
--   A smooth count with `δ < α` puts `≫ X^α / log X` elements of `S` in `(X, 2X]`.
--
--   Source: https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Smooth.lean#L98-L148
-- source:
--   https://github.com/BingoBaggins/deleted-primes/blob/8018e151c53b7ca4ffb0035ca3f455f1254bcdc8/DeletedPrimes/Smooth.lean#L98-L148

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Smooth
set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical

theorem DeletedPrimes.smooth_lower {S : Set ℕ} {α δ c₀ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδα : δ < α)
    (hc₀ : 0 < c₀) (hπ : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |(piS S x : ℝ) - c₀ * liAlpha α x| ≤ C * x ^ δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, c * X ^ α / Real.log X ≤ intervalCount S X := by sorry
