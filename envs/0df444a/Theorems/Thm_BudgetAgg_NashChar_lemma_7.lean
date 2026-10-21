-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_lemma_7
-- name    : BudgetAgg.NashChar.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:36.239224+00:00
-- url     : https://prove2.me/theorems/e1365097-f59e-4c5f-bf63-3c2f1b21502c
-- title:
--   Lemma 7, p. 31 — efficient distributions with the same utility vector coincide
-- statement:
--   Let $P$ be a profile with Leontief utilities, and let $q,q'\in\Delta^m$ both be efficient at $P$. If they induce the same utility vector, that is
--   $$u_i(q)=u_i(q')\qquad\text{for all } i\in N,$$
--   then $q=q'$. Efficient outcomes are therefore determined by their utility vectors. The paper cites this result from Brandt et al. (2025, Lemma 3).
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 31, Lemma 7 (citing Brandt et al. 2025, Lem. 3)

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Lemma 7, p. 31: efficient distributions with equal utility vectors coincide. -/
theorem lemma_7 {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q q' : stdSimplex ℝ (Fin m))
    (hq : IsEfficient P q) (hq' : IsEfficient P q')
    (hu : ∀ i, leontief (P i) q.1 = leontief (P i) q'.1) : q = q' := by sorry

end BudgetAgg.NashChar
