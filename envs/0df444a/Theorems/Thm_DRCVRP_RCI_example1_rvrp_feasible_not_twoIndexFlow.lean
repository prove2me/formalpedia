-- Prove2me | Theorems.Thm_DRCVRP_RCI_example1_rvrp_feasible_not_twoIndexFlow
-- name    : DRCVRP.RCI.example1_rvrp_feasible_not_twoIndexFlow
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:22:37.055964+00:00
-- url     : https://prove2.me/theorems/8c5a4a1c-c50d-4fc6-a01d-c2cee79691aa
-- title:
--   Example 1: an RVRP($\mathcal P$)-feasible route set violates an RCI of 2VF($\mathcal P$)
-- statement:
--   Consider the instance of Example 1: $n=2$ customers, $m=2$ vehicles of capacity $Q=1$, risk level $\epsilon=0.1$, and the ambiguity set $\mathcal P$ of all distributions on $\mathbb R^2$ under which each customer's demand is $1$ with probability $0.925$ and $2$ with probability $0.075$. Let $\mathbf R=(\mathbf R_1,\mathbf R_2)$ with $\mathbf R_1=(1)$, $\mathbf R_2=(2)$, and let $\mathbb P^\star$ be the distribution of Example 1. Then:
--
--   1. $\mathbf R$ is feasible in RVRP($\mathcal P$);
--   2. $\mathbb P^\star\in\mathcal P$ and $\mathbb P^\star\text{-VaR}_{1-\epsilon}[\tilde q_1+\tilde q_2]=3$;
--   3. $$d_{\mathcal P}(\{1,2\})\ge 3;$$
--   4. the arc vector induced by $\mathbf R$ via (3) is infeasible in 2VF($\mathcal P$).
--
--   Hence RVRP($\mathcal P$) and 2VF($\mathcal P$) are not equivalent on this instance: some hypothesis beyond the definition of $d_{\mathcal P}$ is needed for Theorem 1.
--
--   **Formalization Note** Customers are 0-based: the route set is `![[0], [1]]` and $\{1,2\}$ is `{0, 1}`. The level $1-\epsilon$ is written `1 - 0.1`.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 721, Example 1

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_RCI_RouteSet
import Definitions.Def_DRCVRP_RCI_DemandEstimator
import Definitions.Def_DRCVRP_RCI_Formulations
import Definitions.Def_DRCVRP_RCI_Example1

open MeasureTheory

namespace DRCVRP.RCI

/-- Example 1, §3, p. 721: with `n = 2` customers, `m = 2` vehicles, `Q = 1`, `ε = 0.1` and the
ambiguity set of Example 1, the route set `R_1 = (1)`, `R_2 = (2)` is feasible in RVRP(𝒫); the
distribution `ℙ⋆` belongs to 𝒫 and has `ℙ⋆-VaR_{1-ε}[q̃_1 + q̃_2] = 3`; `d_𝒫({1,2}) ≥ 3`; and the
flow induced by `R` is infeasible in 2VF(𝒫). Customers are 0-based (`0, 1 : Fin 2`). -/
theorem example1_rvrp_feasible_not_twoIndexFlow :
    RVRPFeasible example1AmbiguitySet 0.1 1 (![[0], [1]] : Fin 2 → List (Fin 2)) ∧
    example1PStar ∈ example1AmbiguitySet ∧
    MultistageStochastic.valueAtRisk example1PStar (fun q => q 0 + q 1) (1 - 0.1) = 3 ∧
    3 ≤ demandEstimator example1AmbiguitySet 0.1 1 {0, 1} ∧
    ¬ TwoIndexFeasible example1AmbiguitySet 0.1 1 2
      (inducedFlow (![[0], [1]] : Fin 2 → List (Fin 2))) := by sorry

end DRCVRP.RCI
