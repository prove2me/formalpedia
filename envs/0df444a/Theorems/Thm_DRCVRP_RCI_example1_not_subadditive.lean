-- Prove2me | Theorems.Thm_DRCVRP_RCI_example1_not_subadditive
-- name    : DRCVRP.RCI.example1_not_subadditive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:23:53.479329+00:00
-- url     : https://prove2.me/theorems/75e702c3-fe59-4dd4-851a-56b20297ea5f
-- title:
--   Example 1 (continued): the demand estimator violates subadditivity
-- statement:
--   For the ambiguity set $\mathcal P$ of Example 1 (each of the two customer demands equals $1$ with probability $0.925$ and $2$ with probability $0.075$, joint law unrestricted), with $\epsilon=0.1$ and $Q=1$,
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{0.9}(\tilde q_1)=\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{0.9}(\tilde q_2)=1,
--   \qquad \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{0.9}(\tilde q_1+\tilde q_2)\ge 3 ,
--   $$
--   so that the worst-case VaR of the sum exceeds the sum $2$ of the individual worst-case VaRs, and the demand estimator violates condition (S):
--   $$
--   d_{\mathcal P}(\{1\}\cup\{2\})\not\le d_{\mathcal P}(\{1\})+d_{\mathcal P}(\{2\}) .
--   $$
--
--   Together with Example 1 this shows that the failure of Theorem 1's conclusion on this instance comes with a failure of its hypothesis (S).
--
--   **Formalization Note** Customers are 0-based ($\{1\},\{2\}$ are `{0}, {1}`). The worst-case VaR is the real `sSup` of the mission's `worstCaseVaR`; here the VaR values are bounded by $4$, so it is the paper's supremum.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 722, Example 1 (continued)

import Mathlib
import Definitions.Def_DRCVRP_RCI_DemandEstimator
import Definitions.Def_DRCVRP_RCI_Example1

open MeasureTheory

namespace DRCVRP.RCI

/-- Example 1 (continued), §3, p. 722: for the ambiguity set of Example 1 and `ε = 0.1`,
`sup_ℙ ℙ-VaR_{0.9}(q̃_1) = sup_ℙ ℙ-VaR_{0.9}(q̃_2) = 1`, while
`sup_ℙ ℙ-VaR_{0.9}(q̃_1 + q̃_2) ≥ 3 > sup_ℙ ℙ-VaR_{0.9}(q̃_1) + sup_ℙ ℙ-VaR_{0.9}(q̃_2) = 2`;
hence, with `Q = 1`, `d_𝒫({1} ∪ {2}) ≰ d_𝒫({1}) + d_𝒫({2})`. Customers are 0-based. -/
theorem example1_not_subadditive :
    worstCaseVaR example1AmbiguitySet 0.1 {0} = 1 ∧
    worstCaseVaR example1AmbiguitySet 0.1 {1} = 1 ∧
    3 ≤ worstCaseVaR example1AmbiguitySet 0.1 {0, 1} ∧
    worstCaseVaR example1AmbiguitySet 0.1 {0} + worstCaseVaR example1AmbiguitySet 0.1 {1} <
      worstCaseVaR example1AmbiguitySet 0.1 {0, 1} ∧
    ¬ (demandEstimator example1AmbiguitySet 0.1 1 ({0} ∪ {1}) ≤
        demandEstimator example1AmbiguitySet 0.1 1 {0} +
          demandEstimator example1AmbiguitySet 0.1 1 {1}) := by sorry

end DRCVRP.RCI
