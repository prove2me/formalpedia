-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_lemma_2
-- name    : BudgetAgg.NashChar.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:35.211221+00:00
-- url     : https://prove2.me/theorems/b90a54d9-f30e-4e94-8f05-c3c18e05ddc9
-- title:
--   Lemma 2, p. 23 — core fair share guarantees every agent Leontief utility at least 1/n
-- statement:
--   Let $P$ be a profile with Leontief utilities and let $q\in\Delta^m$ satisfy core fair share. Then every agent's utility is at least $1/n$:
--   $$u_i(q)\ \ge\ \frac1n\qquad\text{for all } i\in N.$$
--   The bound comes from comparing with what a single agent can secure with her share $1/n$ of the budget. It is used in Lemma 4.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. Core fair share quantifies over **nonempty** coalitions: in the paper's literal Definition 3 the empty coalition would satisfy the blocking condition vacuously, so no distribution would have core fair share. Division $1/n$ is real division.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 23, Lemma 2

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Lemma 2, p. 23: under core fair share every agent gets Leontief utility at least `1/n`. -/
theorem lemma_2 {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (h : IsCoreFairShare P q) (i : Fin n) :
    1 / (n : ℝ) ≤ leontief (P i) q.1 := by sorry

end BudgetAgg.NashChar
