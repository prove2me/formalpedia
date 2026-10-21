-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_lemma_6
-- name    : BudgetAgg.NashChar.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:32.060961+00:00
-- url     : https://prove2.me/theorems/fbbaefbc-819f-4465-874f-bec23af3c280
-- title:
--   Lemma 6, p. 31 — a distribution maximizes the Nash product iff it has a decomposition supported on critical alternatives
-- statement:
--   Let $P$ be a profile with Leontief utilities and $q\in\Delta^m$. Then $q$ maximizes the Nash product $\prod_{i\in N}u_i$ over $\Delta^m$ if and only if there are nonnegative vectors $(s_i)_{i\in N}$ with
--   $$\sum_{i\in N}s_{i,j}=q_j\ \ (j\in M),\qquad \sum_{j\in M}s_{i,j}=\frac1n\ \ (i\in N),\qquad s_{i,j}=0\ \text{ whenever } j\notin T_{q,i}.$$
--   In words: $q$ splits into equal shares $1/n$, one per agent, each spent only on that agent's critical alternatives. The paper cites this certificate from Brandt et al. (2025, Sec. 4.3); it is the tool behind Lemma 11.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. "$q = NASH(P)$" is written as the predicate `IsNashOutcome P q` ($q\in\Delta^m$ maximizes the Nash product over $\Delta^m$); uniqueness of the maximizer is the separate item `nash_unique`.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 31, Lemma 6 (citing Brandt et al. 2025, Sec. 4.3); decomposition Definition 13, pp. 30–31

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Lemma 6, p. 31 (Brandt et al. 2025, Sec. 4.3): a distribution maximizes the Nash
product iff it has a decomposition in which each agent's share sits on her critical
alternatives. -/
theorem lemma_6 {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m)) :
    IsNashOutcome P q.1 ↔
      ∃ s : Fin n → Fin m → ℝ, IsDecomposition q.1 s ∧
        ∀ i j, j ∉ crit (P i) q.1 → s i j = 0 := by sorry

end BudgetAgg.NashChar
