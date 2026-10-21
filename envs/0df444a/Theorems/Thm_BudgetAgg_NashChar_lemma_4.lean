-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_lemma_4
-- name    : BudgetAgg.NashChar.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:30.968032+00:00
-- url     : https://prove2.me/theorems/506d4740-4e8e-4d53-98c4-6aee9ee9ca0b
-- title:
--   Lemma 4, p. 24 — under core fair share, an alternative is unfunded exactly when no agent values it
-- statement:
--   Let $P$ be a profile with Leontief utilities and let $q\in\Delta^m$ satisfy core fair share. Then for every alternative $j\in M$,
--   $$q_j=0\iff p_{i,j}=0\ \text{ for all } i\in N.$$
--   Thus a core-fair outcome funds exactly the alternatives that some agent wants. The proof of Theorem 3 uses this when it sets up the key profile $P^*$ (p. 33).
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. Core fair share quantifies over **nonempty** coalitions: in the paper's literal Definition 3 the empty coalition would satisfy the blocking condition vacuously, so no distribution would have core fair share.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 24, Lemma 4

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Lemma 4, p. 24: under core fair share an alternative gets nothing exactly when
no agent's peak values it. -/
theorem lemma_4 {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (h : IsCoreFairShare P q) (j : Fin m) :
    q.1 j = 0 ↔ ∀ i, (P i).1 j = 0 := by sorry

end BudgetAgg.NashChar
