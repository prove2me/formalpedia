-- Prove2me | Theorems.Thm_AssortSearch_Cannibal_theorem_2
-- name    : AssortSearch.Cannibal.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:36.513681+00:00
-- url     : https://prove2.me/theorems/602b222c-38f1-49f6-9ec3-508bad583e3b
-- title:
--   Theorem 2 — for $i\in S\subsetneq S^+$, $q_i^{si}(S)>q_i^{si}(S^+)$: demand falls strictly as the assortment expands
-- statement:
--   Let $\mu>0$ and let the consumer's shocks be i.i.d. zero-mean Gumbel with scale $\mu$. In the independent assortment search model, with any utilities, no-purchase utility $u_0$, search utility $u_r$ and search cost $b$: for all assortments $S$ and $S^+$ with $i\in S\subsetneq S^+$,
--   $$
--   q_i^{si}(S)\ >\ q_i^{si}(S^+).
--   $$
--   Variant $i$'s demand decreases as the assortment is expanded in the independent assortment model. Adding variants lowers the no-search demand $q_i^m(S)$ but raises the search adjustment factor $1-H(\bar U,S)$; the theorem says that the first effect dominates, so cannibalization persists in the presence of search.
--
--   **Formalization Note** The paper's "$S\subset S^+$" is strict inclusion. Demand is the probability of the choice event of the random-utility model (not the closed form (3)).
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 9 (PDF 11), Theorem 2

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model

open MeasureTheory ProbabilityTheory

namespace AssortSearch.Cannibal

/-- **Theorem 2**, p. 9: for all `S` and `S⁺` with `i ∈ S ⊂ S⁺` (strict inclusion),
`q_i^si(S) > q_i^si(S⁺)`: variant `i`'s demand decreases as the assortment is expanded in the
independent assortment model. -/
theorem theorem_2 {n : ℕ} (μ : ℝ) (hμ : 0 < μ) (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : IsZeroMeanGumbel μ G) (ur b : ℝ) (w : Fin n → ℝ) (u0 : ℝ) (S Splus : Finset (Fin n))
    (i : Fin n) (hi : i ∈ S) (hS : S ⊂ Splus) :
    searchProb G ur b w u0 S i > searchProb G ur b w u0 Splus i := by sorry

end AssortSearch.Cannibal
