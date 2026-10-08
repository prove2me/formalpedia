-- Prove2me | Theorems.Thm_DiscountedDP_Stationary_theorem7a_essentially_countable
-- name    : DiscountedDP.Stationary.theorem7a_essentially_countable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:40:09.659359+00:00
-- url     : https://prove2.me/theorems/3d46e65b-1d55-449d-a7b8-33d06c2793b3
-- title:
--   Theorem 7(a) — essential countability and the optimality equation
-- statement:
--   Suppose every action at every state is equivalent to a rule of a Markov plan $\pi$. Let $u^*$ be the fixed point of $U_\pi$. Then $u^*$ is the pointwise optimal return over all randomized history-dependent plans, and on every $u\in M(S)$,
--
--   $$U_\pi u=\sup_{a\in A}T_au.$$
--
--   Consequently $u^*$ is the unique bounded Borel solution of $u=\sup_aT_au$. For every $\varepsilon>0$ there is a measurable stationary rule whose plan is $\varepsilon$-optimal at every state against every plan.
--
--   This identifies the optimality equation in the essentially countable case without assuming that the action set itself is countable.
--
--   **Formalization Note** The fixed point is specified by $U_\pi u^*=u^*$ and bounded Borel membership; Theorem 5 supplies its existence. Equivalence of actions uses pointwise reward equality and equality of transition measures.
-- source:
--   Blackwell, Discounted Dynamic Programming, Ann. Math. Statist. 36 (1965), p. 234 (PDF 9), Theorem 7(a)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell (1965), Theorem 7(a), p. 234. The four claims are kept together:
the optimal return, equality of operators, uniqueness of the bounded Borel
solution, and existence of pointwise ε-optimal stationary plans. -/
theorem theorem7a_essentially_countable
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (π : MarkovPlan S A) (hπ : EssCountable P π)
    (ustar : S → ℝ) (hu : IsBM ustar)
    (hfix : ∀ s, U P π ustar s = ustar s) :
    (∀ s, ustar s = optReturn P s) ∧
    (∀ u, IsBM u → ∀ s, U P π u s = ⨆ a : A, Ta P a u s) ∧
    (∀ v, IsBM v → (∀ s, v s = ⨆ a : A, Ta P a v s) → v = ustar) ∧
    (∀ ε : ℝ, 0 < ε → ∃ f : {g : S → A // Measurable g},
      IsEOptimal P ε (stationary f).toPlan) := by sorry

end DiscountedDP.Stationary
