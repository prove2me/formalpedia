-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_nash_unique
-- name    : BudgetAgg.NashChar.nash_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:38.200012+00:00
-- url     : https://prove2.me/theorems/cb4b07a6-7aa0-4491-8f32-3c36157fcacc
-- title:
--   §6, p. 16 — the Nash product rule returns exactly one distribution
-- statement:
--   Let $P$ be a profile of peaks with Leontief utilities $u_1,\dots,u_n$. Then the Nash product has exactly one maximizer over the simplex:
--   $$\exists!\,q\in\Delta^m:\quad \prod_{i\in N}u_i(q)=\max_{q'\in\Delta^m}\prod_{i\in N}u_i(q').$$
--   This is the statement on p. 16 that "NASH is well-defined as it always returns exactly one distribution"; the paper cites it from Brandt et al. (2025). It makes the predicate "q is a Nash outcome at $P$" equivalent to "$q=NASH(P)$".
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 16, §6, unnumbered statement 'NASH is well-defined as it always returns exactly one distribution (Brandt et al., 2025).'

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- §6, p. 16: NASH returns exactly one distribution. -/
theorem nash_unique {n m : ℕ} [NeZero n] [NeZero m] (P : Profile n m) :
    ∃! q : stdSimplex ℝ (Fin m), IsNashOutcome P q.1 := by sorry

end BudgetAgg.NashChar
