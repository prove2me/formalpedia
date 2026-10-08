-- Prove2me | Theorems.Thm_DiscountedDP_Stationary_theorem6b_p_optimal_stationary
-- name    : DiscountedDP.Stationary.theorem6b_p_optimal_stationary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T01:39:44.727687+00:00
-- url     : https://prove2.me/theorems/415c7adc-290c-4dfb-b72f-dfe2fd674023
-- title:
--   Theorem 6(b) — a (p, ε)-optimal stationary plan exists
-- statement:
--   Let $p$ be a probability distribution on the initial state space and $\varepsilon>0$. There is a measurable stationary rule $f$ such that, for every randomized history-dependent plan $\pi$,
--
--   $$p\{s:I(\pi)(s)>I(f^{(\infty)})(s)+\varepsilon\}=0.$$
--
--   Thus stationary plans achieve the paper's distribution-dependent approximate optimality, even when a uniformly $\varepsilon$-optimal plan need not exist.
--
--   **Formalization Note** $p$ is explicitly a probability measure. The event uses the paper's strict inequality and is quantified over all plans, including randomized history-dependent ones.
-- source:
--   Blackwell, Discounted Dynamic Programming, Ann. Math. Statist. 36 (1965), p. 232 (PDF 7), Theorem 6(b)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell (1965), Theorem 6(b), p. 232. -/
theorem theorem6b_p_optimal_stationary
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (p : Measure S) [IsProbabilityMeasure p]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : {g : S → A // Measurable g},
      IsPOptimal P p ε (stationary f).toPlan := by sorry

end DiscountedDP.Stationary
