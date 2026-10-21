-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_nash_efficient_gsp
-- name    : BudgetAgg.NashChar.nash_efficient_gsp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:40.176131+00:00
-- url     : https://prove2.me/theorems/eabe7307-5aa4-4374-a3de-f3cf0c98911f
-- title:
--   §6, p. 16 — NASH is efficient and group-strategyproof
-- statement:
--   Let $g$ be the Nash product rule, i.e. a mechanism such that $g(P)$ maximizes $\prod_{i\in N}u_i$ over $\Delta^m$ for every profile $P$. Then
--   1. $g$ is efficient: $g(P)$ is Pareto efficient at $P$ for every $P$;
--   2. $g$ is group-strategyproof: for every $N'\subseteq N$ and profiles $P,P'$ agreeing outside $N'$, either some $i\in N'$ has $u_i(g(P))>u_i(g(P'))$ or every $i\in N'$ has $u_i(g(P))=u_i(g(P'))$, utilities taken at the true peaks of $P$.
--
--   The paper cites this from Brandt et al. (2025); its footnote 4 explains that the cited notion of group-strategyproofness allows more manipulations and so implies the one used here. Group-strategyproofness of NASH is part of the existence half of Theorem 3.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. "$q = NASH(P)$" is written as the predicate `IsNashOutcome P q` ($q\in\Delta^m$ maximizes the Nash product over $\Delta^m$); uniqueness of the maximizer is the separate item `nash_unique`.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 16, §6, unnumbered statement 'In addition, NASH is efficient and group-strategyproof (Brandt et al., 2025).' (footnote 4)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- §6, p. 16 (citing Brandt et al. 2025): NASH is efficient and group-strategyproof. -/
theorem nash_efficient_gsp {n m : ℕ} [NeZero n] [NeZero m]
    (g : Mechanism n m) (hg : ∀ P, IsNashOutcome P (g P).1) :
    (∀ P, IsEfficient P (g P)) ∧ IsGroupSP g := by sorry

end BudgetAgg.NashChar
