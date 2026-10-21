-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_theorem_3
-- name    : BudgetAgg.NashChar.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:43.546019+00:00
-- url     : https://prove2.me/theorems/0ac74e99-1b83-43c5-8bd0-1f78e049f0fc
-- title:
--   Theorem 3, p. 16 — with Leontief utilities, NASH is the only continuous mechanism satisfying group-strategyproofness and core fair share
-- statement:
--   Agents $N=[n]$ report peaks $p_i\in\Delta^m$ and have Leontief utilities $u_i(q)=\min_{j:\,p_{i,j}>0}q_j/p_{i,j}$. For every mechanism $f:(\Delta^m)^n\to\Delta^m$ the following are equivalent:
--   1. $f$ is continuous, group-strategyproof, and $f(P)$ satisfies core fair share at every profile $P$;
--   2. $f=NASH$, i.e. for every profile $P$,
--   $$f(P)\in\arg\max_{q\in\Delta^m}\ \prod_{i\in N}u_i(q).$$
--
--   The direction (2)⇒(1) says NASH has the three properties (Propositions 1 and 2 and the cited group-strategyproofness); (1)⇒(2) says nothing else has them. Since the maximizer is unique, (2) determines $f$. Each axiom is needed: constant mechanisms are continuous and group-strategyproof, and the paper shows the other two cannot be dropped either.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. Core fair share quantifies over **nonempty** coalitions: in the paper's literal Definition 3 the empty coalition would satisfy the blocking condition vacuously, so no distribution would have core fair share. "$q = NASH(P)$" is written as the predicate `IsNashOutcome P q` ($q\in\Delta^m$ maximizes the Nash product over $\Delta^m$); uniqueness of the maximizer is the separate item `nash_unique`. Continuity is `Continuous f` on the subtype $(\Delta^m)^n$, equivalent to Definition 7's $\ell_1$ formulation. Group-strategyproofness evaluates both outcomes with the true peaks.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 16, Theorem 3 (restated p. 33, proof pp. 33–36, App. E.2)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Theorem 3, p. 16: Nash is exactly the continuous, group-strategyproof, core-fair rule. -/
theorem theorem_3 {n m : ℕ} [NeZero n] [NeZero m] (f : Mechanism n m) :
    (Continuous f ∧ IsGroupSP f ∧ ∀ P, IsCoreFairShare P (f P)) ↔
      (∀ P, IsNashOutcome P (f P).1) := by sorry

end BudgetAgg.NashChar
