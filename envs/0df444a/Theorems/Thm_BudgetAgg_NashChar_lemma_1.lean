-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_lemma_1
-- name    : BudgetAgg.NashChar.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:13.505561+00:00
-- url     : https://prove2.me/theorems/a431c789-8ea9-4170-b94e-7e64e6d8af2e
-- title:
--   Lemma 1, p. 22 — with Leontief utilities, efficiency means every funded alternative is critical for someone
-- statement:
--   Let $P$ be a profile with Leontief utilities and $q\in\Delta^m$. Then $q$ is efficient if and only if every alternative it funds is critical for some agent:
--   $$q\ \text{efficient}\iff \forall j\in M:\ q_j>0\ \Rightarrow\ \exists i\in N,\ j\in T_{q,i}.$$
--   The paper cites this characterization from Brandt et al. (2025, Lemma 2). It is used in the proof of Lemma 3.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 22, Lemma 1 (citing Brandt et al. 2025, Lem. 2)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Lemma 1, p. 22 (Brandt et al. 2025, Lem. 2): a distribution is efficient iff every
alternative it funds is critical for some agent. -/
theorem lemma_1 {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m)) :
    IsEfficient P q ↔ ∀ j, 0 < q.1 j → ∃ i, j ∈ crit (P i) q.1 := by sorry

end BudgetAgg.NashChar
