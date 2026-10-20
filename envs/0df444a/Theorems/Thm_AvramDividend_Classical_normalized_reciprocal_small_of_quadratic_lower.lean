-- Prove2me | Theorems.Thm_AvramDividend_Classical_normalized_reciprocal_small_of_quadratic_lower
-- name    : AvramDividend.Classical.normalized_reciprocal_small_of_quadratic_lower
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T22:17:13.290596+00:00
-- url     : https://prove2.me/theorems/0339d591-089e-4782-923c-12d6bde23aef
-- title:
--   A positive quadratic exponent lower bound makes the normalised reciprocal arbitrarily small
-- statement:
--   Suppose ψ(θ)-q is bounded below by a positive multiple aθ² for all θ above β. Given ε>0, take θ above β, 1 and (aε)⁻¹. The reciprocal denominator is positive and θ/(ψ(θ)-q) < ε. This proves the small-transform hypothesis needed to deduce W(0)=0 from the verified Laplace-origin theorem.
-- source:
--   Elementary ordered-field inequalities; application to the q-scale Laplace transform and Gaussian Lévy exponent coercivity.

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem AvramDividend.Classical.normalized_reciprocal_small_of_quadratic_lower
    (ψ : ℝ → ℝ) (q a β : ℝ) (ha : 0 < a)
    (hbound : ∀ θ : ℝ, β ≤ θ → a * θ ^ 2 ≤ ψ θ - q) :
    ∀ ε : ℝ, 0 < ε →
      ∃ θ : ℝ, β ≤ θ ∧ 0 < θ ∧ θ * (ψ θ - q)⁻¹ < ε := by sorry
