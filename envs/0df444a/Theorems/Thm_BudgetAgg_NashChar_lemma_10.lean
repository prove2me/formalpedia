-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_lemma_10
-- name    : BudgetAgg.NashChar.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:40.341033+00:00
-- url     : https://prove2.me/theorems/08e7d218-09da-4c51-abbb-98a54df67cb3
-- title:
--   Lemma 10, p. 35 — core fair share forces the Nash outcome when every peak lives on its critical alternatives
-- statement:
--   Let $P^*$ be a profile with Leontief utilities and $q\in\Delta^m$ a distribution such that every agent values every non-critical alternative at $0$:
--   $$j\notin T^*_{q,i}\ \Longrightarrow\ p^*_{i,j}=0\qquad (i\in N,\ j\in M).$$
--   If $q$ satisfies core fair share at $P^*$, then $q=NASH(P^*)$, i.e. $q$ maximizes $\prod_i u^*_i$ over $\Delta^m$.
--
--   This is the second equality in the proof of Theorem 3: the key profile of Lemma 9 satisfies the hypothesis.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. Core fair share quantifies over **nonempty** coalitions: in the paper's literal Definition 3 the empty coalition would satisfy the blocking condition vacuously, so no distribution would have core fair share. "$q = NASH(P)$" is written as the predicate `IsNashOutcome P q` ($q\in\Delta^m$ maximizes the Nash product over $\Delta^m$); uniqueness of the maximizer is the separate item `nash_unique`.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 35, Lemma 10 (proof p. 36)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Lemma 10, p. 35: the core condition forces Nash optimality at a critical-support profile. -/
theorem lemma_10 {n m : ℕ} [NeZero n] [NeZero m]
    (Ps : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hsupp : ∀ i j, j ∉ crit (Ps i) q.1 → (Ps i).1 j = 0)
    (hcore : IsCoreFairShare Ps q) : IsNashOutcome Ps q.1 := by sorry

end BudgetAgg.NashChar
