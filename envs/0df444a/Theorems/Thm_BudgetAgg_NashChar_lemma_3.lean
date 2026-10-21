-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_lemma_3
-- name    : BudgetAgg.NashChar.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:48.765076+00:00
-- url     : https://prove2.me/theorems/e1f39239-e5c3-4af8-bc33-5b3ddf27560d
-- title:
--   Lemma 3, p. 24 — a sufficient condition for core fair share
-- statement:
--   Let $P$ be a profile with Leontief utilities and $q\in\Delta^m$. If for every group $G\subseteq N$ the alternatives critical to some member of $G$ receive at least the group's share,
--   $$q(T_{q,G})=\sum_{j\in T_{q,G}}q_j\ \ge\ \frac{|G|}{n}\qquad\text{for all } G\subseteq N,$$
--   then $q$ satisfies core fair share. (The case $G=\emptyset$ reads $0\ge0$.) The converse fails already for $n=m=2$ (p. 24).
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. Core fair share quantifies over **nonempty** coalitions: in the paper's literal Definition 3 the empty coalition would satisfy the blocking condition vacuously, so no distribution would have core fair share. $|G|/n$ is real division.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 24, Lemma 3

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Lemma 3, p. 24: if every group's critical alternatives receive at least the group's
share `|G|/n`, then core fair share holds. -/
theorem lemma_3 {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (h : ∀ G : Finset (Fin n), (G.card : ℝ) / (n : ℝ) ≤ ∑ j ∈ critG P q.1 G, q.1 j) :
    IsCoreFairShare P q := by sorry

end BudgetAgg.NashChar
