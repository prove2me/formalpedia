-- Prove2me | Theorems.Thm_BudgetAgg_NashChar_lemma_8
-- name    : BudgetAgg.NashChar.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:00:44.307197+00:00
-- url     : https://prove2.me/theorems/bc8964b4-15d5-4e2f-92c0-c422905885cb
-- title:
--   Lemma 8, p. 31 — an efficient distribution gives no alternative more than the largest peak coordinate
-- statement:
--   Let $P$ be a profile with Leontief utilities, and let $q\in\Delta^m$ be efficient at $P$. Then
--   $$q_j\ \le\ \max_{i\in N}p_{i,j}\qquad\text{for all } j\in M.$$
--   This is one direction of range-respect; NASH need not respect the lower bound $\min_i p_{i,j}$. It is used in the proof of Proposition 1. The paper adds that the bound holds in particular for any outcome of NASH, which follows from the efficiency of NASH.
--
--   **Formalization Note** Agents and alternatives are indexed from $0$ (`Fin n`, `Fin m`); distributions are points of Mathlib's `stdSimplex ℝ (Fin m)`; all values are real. The paper's convention that $n$ and $m$ are positive integers (p. 6) is the hypothesis `[NeZero n] [NeZero m]`. The maximum is `Finset.univ.sup'` over the nonempty set of agents. Only the first sentence of the lemma is stated here.
-- source:
--   Brandt, Greger, Segal-Halevi, Suksompong, Optimal Budget Aggregation with Star-Shaped Preference Domains, arXiv:2402.15904v3, p. 31, Lemma 8

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting

namespace BudgetAgg.NashChar

/-- Lemma 8, p. 31: an efficient distribution never gives an alternative more than the
largest peak coordinate for it. -/
theorem lemma_8 {n m : ℕ} [NeZero n] [NeZero m]
    (P : Profile n m) (q : stdSimplex ℝ (Fin m))
    (hq : IsEfficient P q) (j : Fin m) :
    q.1 j ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => (P i).1 j) := by sorry

end BudgetAgg.NashChar
