-- Prove2me | Theorems.Thm_DiscountedDP_Stationary_theorem7b_optimal_stationary
-- name    : DiscountedDP.Stationary.theorem7b_optimal_stationary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:40:23.656511+00:00
-- url     : https://prove2.me/theorems/bc483f2b-c52a-4fc8-85a4-d8d0ed82f6f8
-- title:
--   Theorem 7(b) — an optimal stationary plan under essential finiteness
-- statement:
--   Suppose a Markov plan $\pi=(f_1,f_2,\ldots)$ makes the action set essentially finite: on each piece $S_n$ of a countable Borel partition, every action is equivalent at its state to one of $f_1(s),\ldots,f_n(s)$. Then there is a measurable rule $f:S\to A$ whose stationary plan is optimal:
--
--   $$I(\pi')(s)\le I(f^{(\infty)})(s)\qquad\text{for every plan }\pi'\text{ and every }s\in S.$$
--
--   A plan in the comparison class may randomize and depend on its entire observed history. The theorem includes finite action sets through an enumeration by constant rules.
--
--   **Formalization Note** The partition is Borel, its pieces may be empty, and on Lean's zero-based piece $n$ the permitted rules have indices $0,\ldots,n$. This corresponds to the paper's piece $S_{n+1}$ and rules $f_1,\ldots,f_{n+1}$. Action equivalence is the paper's primary reward-and-transition definition.
-- source:
--   Blackwell, Discounted Dynamic Programming, Ann. Math. Statist. 36 (1965), p. 234 (PDF 9), Theorem 7(b)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators

namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

/-- Blackwell (1965), Theorem 7(b), p. 234: essential finiteness yields
a stationary plan optimal among all randomized history-dependent plans. -/
theorem theorem7b_optimal_stationary
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (π : MarkovPlan S A) (hπ : EssFinite P π) :
    ∃ f : {g : S → A // Measurable g},
      IsOptimal P (stationary f).toPlan := by sorry

end DiscountedDP.Stationary
