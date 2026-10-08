-- Prove2me | Theorems.Thm_DiscountedDP_Stationary_theorem5_contraction
-- name    : DiscountedDP.Stationary.theorem5_contraction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:39:56.969467+00:00
-- url     : https://prove2.me/theorems/45e2a098-6311-4935-8ff5-c26f352bb540
-- title:
--   Theorem 5 — monotonicity and constant shifts imply a β-contraction
-- statement:
--   Let $V:M(S)\to M(S)$ be any operator, with $0\le\beta<1$. Suppose $V$ preserves pointwise order and $V(u+c)=Vu+\beta c$ for every bounded Borel $u$ and constant $c$. Then
--
--   $$\|Vu-Vv\|_\infty\le\beta\|u-v\|_\infty.$$
--
--   Moreover, $V$ has a unique fixed point $u^*\in M(S)$, and for every $u\in M(S)$ and $n\ge0$,
--
--   $$\|V^nu-u^*\|_\infty\le\beta^n\|u-u^*\|_\infty.$$
--
--   This criterion is used for the operators associated with decision rules and Markov plans.
--
--   **Formalization Note** $M(S)$ is the bounded measurable functions, and the supremum norm is over every state. The abstract operator has no policy parameter. The conclusion includes both existence and uniqueness of the bounded Borel fixed point.
-- source:
--   Blackwell, Discounted Dynamic Programming, Ann. Math. Statist. 36 (1965), p. 232 (PDF 7), Theorem 5

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell (1965), Theorem 5, p. 232. The abstract operator acts on
bounded Borel functions; its two properties are monotonicity and constant shifts. -/
theorem theorem5_contraction
    {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (V : (S → ℝ) → S → ℝ)
    (hmap : ∀ u, IsBM u → IsBM (V u))
    (hmono : ∀ u v, IsBM u → IsBM v →
      (∀ s, u s ≤ v s) → ∀ s, V u s ≤ V v s)
    (hshift : ∀ u, IsBM u → ∀ c : ℝ, ∀ s,
      V (fun t => u t + c) s = V u s + β * c) :
    (∀ u v, IsBM u → IsBM v →
      supNorm (fun s => V u s - V v s) ≤
        β * supNorm (fun s => u s - v s)) ∧
    ∃ ustar : S → ℝ, IsBM ustar ∧ (∀ s, V ustar s = ustar s) ∧
      (∀ v, IsBM v → (∀ s, V v s = v s) → v = ustar) ∧
      ∀ u, IsBM u → ∀ n : ℕ,
        supNorm (fun s => (V^[n] u) s - ustar s) ≤
          β ^ n * supNorm (fun s => u s - ustar s) := by sorry

end DiscountedDP.Stationary
