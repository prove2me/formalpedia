-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_theorem_3_uniqueness
-- name    : BudgetAgg.NashChar.theorem_3_uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:56.782932+00:00
-- url     : https://prove2.me/theorems/b5c36a95-a40b-4500-b731-904d219f70ac
-- title:
--   Proof of Theorem 3, p. 36 — a continuous, group-strategyproof mechanism with core fair share is NASH
-- statement:
--   Let $f$ be a mechanism for Leontief utilities that is continuous, group-strategyproof and satisfies core fair share at every profile. Then for every profile $P$,
--   $$f(P)=NASH(P),$$
--   that is, $f(P)$ maximizes $\prod_{i\in N}u_i$ over $\Delta^m$. The paper obtains it as the chain $f(P)=f(P^*)=NASH(P^*)=NASH(P)$ by Lemmas 9, 10 and 11, with $P^*$ the key profile of Lemma 9. This is the uniqueness half of Theorem 3.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. Core fair share quantifies over **nonempty** coalitions: in the paper's literal Definition 3 the empty coalition would satisfy the blocking condition vacuously, so no distribution would have core fair share. "$q = NASH(P)$" is written as the predicate `IsNashOutcome P q` ($q\in\Delta^m$ maximizes the Nash product over $\Delta^m$); uniqueness of the maximizer is the separate item `nash_unique`. Continuity is `Continuous` on the subtype $(\Delta^m)^n$.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 36, proof of Theorem 3

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Proof of Theorem 3, p. 36: a continuous, group-strategyproof mechanism with core fair
share returns the Nash outcome at every profile. -/
theorem theorem_3_uniqueness {n m : ℕ} [NeZero n] [NeZero m]
    (f : Mechanism n m) (hf_cont : Continuous f) (hf_gsp : IsGroupSP f)
    (hf_core : ∀ P, IsCoreFairShare P (f P)) :
    ∀ P, IsNashOutcome P (f P).1 := by sorry

end BudgetAgg.NashChar
