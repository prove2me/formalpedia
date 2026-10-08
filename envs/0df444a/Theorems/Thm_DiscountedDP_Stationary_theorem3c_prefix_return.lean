-- Prove2me | Theorems.Thm_DiscountedDP_Stationary_theorem3c_prefix_return
-- name    : DiscountedDP.Stationary.theorem3c_prefix_return
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:39:21.079974+00:00
-- url     : https://prove2.me/theorems/c8de8bfa-36eb-4d37-9f1b-d05cf9e53ff9
-- title:
--   Theorem 3(c) — prefixing a Markov plan applies the one-step operator
-- statement:
--   Let $f$ be a measurable decision rule and $\pi=(f_1,f_2,\ldots)$ a Markov plan. The plan $(f,\pi)$ uses $f$ on the first day and then follows $\pi$. Their discounted returns satisfy
--
--   $$T_f I(\pi)=I(f,\pi)$$
--
--   at every initial state. This identity relates one-step operators to the paper's discounted series.
--
--   **Formalization Note** Both plans are deterministic kernels within the larger class of history-dependent randomized plans. The operator uses the reward before the first transition and discounts the remaining return by $\beta$.
-- source:
--   Blackwell, Discounted Dynamic Programming, Ann. Math. Statist. 36 (1965), p. 231 (PDF 6), Theorem 3(c)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell (1965), Theorem 3(c), p. 231: prefixing a Markov plan
by a rule applies that rule's one-step operator to its return. -/
theorem theorem3c_prefix_return
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (f : {g : S → A // Measurable g})
    (π : MarkovPlan S A) :
    ∀ s, T P f (I P π.toPlan) s =
      I P (MarkovPlan.cons f π).toPlan s := by sorry

end DiscountedDP.Stationary
