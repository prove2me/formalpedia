-- Prove2me | Theorems.Thm_DRCVRP_RCI_twoIndexFlow_to_rvrp
-- name    : DRCVRP.RCI.twoIndexFlow_to_rvrp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:25:17.773319+00:00
-- url     : https://prove2.me/theorems/c373d58f-1863-4150-ae2f-91628c6f9872
-- title:
--   Theorem 1 (ii): 2VF($\mathcal P$)-feasible flows come from unique RVRP($\mathcal P$)-feasible route sets of equal cost
-- statement:
--   Under the assumptions of Theorem 1 (i) (demands nonnegative almost surely under every $\mathbb P\in\mathcal P$, finite worst-case values-at-risk, $d_{\mathcal P}$ subadditive, $Q>0$, $c\ge 0$, $\epsilon\in(0,1)$), let $x$ be feasible in 2VF($\mathcal P$). Then there is a route set $\mathbf R$ feasible in RVRP($\mathcal P$) that induces $x$ via (3); every route set $\mathbf R'\in\mathfrak P(V_C,m)$ inducing $x$ is a reordering of $\mathbf R$,
--   $$
--   \mathbf R'=(\mathbf R_{\sigma(1)},\dots,\mathbf R_{\sigma(m)})\quad\text{for some permutation }\sigma\text{ of }K ;
--   $$
--   and $\sum_{(i,j)\in A}c(i,j)x_{ij}=c(\mathbf R)$.
--
--   This is the half of Theorem 1 that lets a branch-and-cut algorithm for 2VF($\mathcal P$) solve RVRP($\mathcal P$).
--
--   **Formalization Note** Uniqueness is stated over all route sets inducing $x$; a reordering permutes the routes, never the customers inside a route (routes are directed). Customers are 0-based.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 722, Theorem 1 (ii)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_RCI_RouteSet
import Definitions.Def_DRCVRP_RCI_DemandEstimator
import Definitions.Def_DRCVRP_RCI_Formulations

open MeasureTheory

namespace DRCVRP.RCI

/-- Theorem 1 (ii), p. 722: any solution `x` feasible in 2VF(𝒫) is induced via (3) by a route
set `R` feasible in RVRP(𝒫); every route set inducing `x` equals `R` up to a reordering of the
routes `R_1, …, R_m`; and `x` and `R` attain the same transportation costs.
Standing hypotheses: costs `c(i,j) ≥ 0`, capacity `Q > 0`, `ε ∈ (0,1)`, every `ℙ ∈ 𝒫`
(`Amb`) a probability distribution with `q̃ ≥ 0` `ℙ`-a.s., the worst-case VaR of every customer
set finite (the paper's `d_𝒫` is real valued), and `d_𝒫` subadditive, condition (S). -/
theorem twoIndexFlow_to_rvrp {n m : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (Q : ℝ) (hQ : 0 < Q) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (Amb : Set (Measure (Fin n → ℝ))) (hAmb : ∀ P ∈ Amb, IsProbabilityMeasure P)
    (hnonneg : ∀ P ∈ Amb, ∀ᵐ q ∂P, ∀ i, 0 ≤ q i)
    (hbdd : ∀ S : Finset (Fin n), BddAbove ((fun P => MultistageStochastic.valueAtRisk P
      (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb))
    (hsub : IsSubadditive Amb ε Q) :
    (∀ x : Fin (n + 1) → Fin (n + 1) → ℕ, TwoIndexFeasible Amb ε Q m x →
      ∃ R : Fin m → List (Fin n), RVRPFeasible Amb ε Q R ∧ inducedFlow R = x ∧
        (∀ R' : Fin m → List (Fin n), IsRouteSet R' → inducedFlow R' = x →
          ∃ σ : Equiv.Perm (Fin m), R' = R ∘ σ) ∧
        flowCost c x = routeSetCost c R) := by sorry

end DRCVRP.RCI
