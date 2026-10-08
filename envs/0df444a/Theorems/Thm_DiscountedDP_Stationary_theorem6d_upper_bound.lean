-- Prove2me | Theorems.Thm_DiscountedDP_Stationary_theorem6d_upper_bound
-- name    : DiscountedDP.Stationary.theorem6d_upper_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:39:55.070071+00:00
-- url     : https://prove2.me/theorems/33c051c1-259f-47cc-8e30-0058e5bf76cb
-- title:
--   Theorem 6(d) — a Bellman supersolution bounds every plan
-- statement:
--   Let $u\in M(S)$ be a bounded Borel function. For each action $a$, let $T_a$ be the operator for the constant rule $f(s)=a$. If $T_au\le u$ pointwise for every $a\in A$, then
--
--   $$I(\pi)(s)\le u(s)\qquad\text{for every plan }\pi\text{ and state }s.$$
--
--   This supplies an upper bound on all achievable returns, including those of randomized history-dependent plans.
--
--   **Formalization Note** The hypothesis quantifies over all actions, and the conclusion over all plans. No hypothesis about a fixed point or an optimal plan is added.
-- source:
--   Blackwell, Discounted Dynamic Programming, Ann. Math. Statist. 36 (1965), p. 232 (PDF 7), Theorem 6(d)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell (1965), Theorem 6(d), p. 232. -/
theorem theorem6d_upper_bound
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (u : S → ℝ) (hu : IsBM u)
    (hupper : ∀ a s, Ta P a u s ≤ u s) :
    ∀ π : Plan (S := S) (A := A), ∀ s, I P π s ≤ u s := by sorry

end DiscountedDP.Stationary
