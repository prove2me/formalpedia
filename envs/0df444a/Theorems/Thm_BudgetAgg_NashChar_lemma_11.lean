-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_lemma_11
-- name    : BudgetAgg.NashChar.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:39.597262+00:00
-- url     : https://prove2.me/theorems/f5a19bd1-e0ba-4187-9e1a-aca0fb868495
-- title:
--   Lemma 11, p. 36 — the Nash outcome transfers between profiles with the same critical sets
-- statement:
--   Let $P^*$ and $P$ be profiles with Leontief utilities, and let $q=NASH(P^*)$. If the critical sets of $q$ agree in the two profiles,
--   $$T^*_{q,i}=T_{q,i}\qquad\text{for all } i\in N,$$
--   then $NASH(P)=q$.
--
--   This is the third equality in the proof of Theorem 3.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. "$q = NASH(P)$" is written as the predicate `IsNashOutcome P q` ($q\in\Delta^m$ maximizes the Nash product over $\Delta^m$); uniqueness of the maximizer is the separate item `nash_unique`.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 36, Lemma 11

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Lemma 11, p. 36: Nash optimality transfers when all critical sets agree. -/
theorem lemma_11 {n m : ℕ} [NeZero n] [NeZero m]
    (Ps P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hnash : IsNashOutcome Ps q.1)
    (hcrit : ∀ i, crit (Ps i) q.1 = crit (P i) q.1) :
    IsNashOutcome P q.1 := by sorry

end BudgetAgg.NashChar
