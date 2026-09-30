-- Prove2me | Theorems.Thm_DRCVRP_RCI_rvrp_to_twoIndexFlow
-- name    : DRCVRP.RCI.rvrp_to_twoIndexFlow
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:24:24.308565+00:00
-- url     : https://prove2.me/theorems/434d5ad5-9105-4564-94ad-0d17813c0699
-- title:
--   Theorem 1 (i): RVRP($\mathcal P$)-feasible route sets induce 2VF($\mathcal P$)-feasible flows of equal cost
-- statement:
--   Consider the distributionally robust chance-constrained CVRP on nodes $V=\{0,\dots,n\}$ with depot $0$, $m$ vehicles of capacity $Q>0$, nonnegative arc costs $c(i,j)$, risk level $\epsilon\in(0,1)$ and an ambiguity set $\mathcal P$ of probability distributions of the demand vector $\tilde{\boldsymbol q}$. Assume
--
--   1. $\tilde{\boldsymbol q}\ge\mathbf 0$ $\mathbb P$-almost surely for every $\mathbb P\in\mathcal P$;
--   2. for every customer set $S$ the worst-case value-at-risk $\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}[\sum_{i\in S}\tilde q_i]$ is finite;
--   3. the demand estimator $d_{\mathcal P}$ of (2) satisfies the subadditivity condition (S).
--
--   Then every route set $\mathbf R$ feasible in RVRP($\mathcal P$) induces, via
--   $$
--   x_{ij}=1\iff\exists k\in K,\ \exists l\in\{0,\dots,n_k\}:\ (i,j)=(R_{k,l},R_{k,l+1}),\tag{3}
--   $$
--   a solution $x$ feasible in 2VF($\mathcal P$), and $\sum_{(i,j)\in A}c(i,j)x_{ij}=c(\mathbf R)$.
--
--   This is the half of Theorem 1 that makes the rounded capacity inequalities valid for RVRP($\mathcal P$).
--
--   **Formalization Note** Assumption 2 encodes the paper's declaration that $d_{\mathcal P}$ is real valued; $Q>0$ and $c\ge0$ are the paper's $Q\in\mathbb R_+$, $c(i,j)\in\mathbb R_+$ ($Q>0$ is needed because (2) divides by $Q$). "Induces a unique solution" needs no separate clause: (3) defines $x$ from $\mathbf R$. Customers are 0-based.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 722, Theorem 1 (i)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_RCI_RouteSet
import Definitions.Def_DRCVRP_RCI_DemandEstimator
import Definitions.Def_DRCVRP_RCI_Formulations

open MeasureTheory

namespace DRCVRP.RCI

/-- Theorem 1 (i), p. 722: any route set `R` feasible in RVRP(𝒫) induces via (3) a solution
`x` feasible in 2VF(𝒫), and `x` and `R` attain the same transportation costs.
Standing hypotheses: costs `c(i,j) ≥ 0`, capacity `Q > 0`, `ε ∈ (0,1)`, every `ℙ ∈ 𝒫`
(`Amb`) a probability distribution with `q̃ ≥ 0` `ℙ`-a.s., the worst-case VaR of every customer
set finite (the paper's `d_𝒫` is real valued), and `d_𝒫` subadditive, condition (S). -/
theorem rvrp_to_twoIndexFlow {n m : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (Q : ℝ) (hQ : 0 < Q) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (Amb : Set (Measure (Fin n → ℝ))) (hAmb : ∀ P ∈ Amb, IsProbabilityMeasure P)
    (hnonneg : ∀ P ∈ Amb, ∀ᵐ q ∂P, ∀ i, 0 ≤ q i)
    (hbdd : ∀ S : Finset (Fin n), BddAbove ((fun P => MultistageStochastic.valueAtRisk P
      (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb))
    (hsub : IsSubadditive Amb ε Q) :
    (∀ R : Fin m → List (Fin n), RVRPFeasible Amb ε Q R →
      TwoIndexFeasible Amb ε Q m (inducedFlow R) ∧ flowCost c (inducedFlow R) = routeSetCost c R) := by sorry

end DRCVRP.RCI
