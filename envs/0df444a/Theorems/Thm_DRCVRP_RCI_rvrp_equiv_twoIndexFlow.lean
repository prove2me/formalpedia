-- Prove2me | Theorems.Thm_DRCVRP_RCI_rvrp_equiv_twoIndexFlow
-- name    : DRCVRP.RCI.rvrp_equiv_twoIndexFlow
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:25:46.59385+00:00
-- url     : https://prove2.me/theorems/15f112e4-c7da-43f3-a4e1-5ebff85ed01e
-- title:
--   Theorem 1: under subadditivity, RVRP($\mathcal P$) and 2VF($\mathcal P$) are equivalent
-- statement:
--   Consider the distributionally robust chance-constrained capacitated vehicle routing problem on a complete directed graph with depot $0$ and customers $V_C=\{1,\dots,n\}$, $m$ vehicles of capacity $Q>0$, nonnegative (possibly asymmetric) arc costs $c(i,j)$, risk level $\epsilon\in(0,1)$ and an ambiguity set $\mathcal P$ of probability distributions of the demand vector $\tilde{\boldsymbol q}$. Let $d_{\mathcal P}$ be the demand estimator
--   $$
--   d_{\mathcal P}(S)=\max\left\{\left\lceil\frac1Q\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big]\right\rceil,1\right\}\ (S\neq\emptyset),\qquad d_{\mathcal P}(\emptyset)=0,
--   $$
--   assumed real valued (every worst-case value-at-risk finite). Assume that $\tilde{\boldsymbol q}\ge\mathbf 0$ $\mathbb P$-a.s. for all $\mathbb P\in\mathcal P$ and that $d_{\mathcal P}$ satisfies the subadditivity condition (S): $d_{\mathcal P}(S\cup T)\le d_{\mathcal P}(S)+d_{\mathcal P}(T)$ for all $S,T\subseteq V_C$. Then RVRP($\mathcal P$) and 2VF($\mathcal P$) are equivalent:
--
--   1. any route set $\mathbf R$ feasible in RVRP($\mathcal P$) induces via (3) a solution $x$ feasible in 2VF($\mathcal P$), and $x$ and $\mathbf R$ attain the same transportation costs;
--   2. any solution $x$ feasible in 2VF($\mathcal P$) is induced via (3) by a route set $\mathbf R$ feasible in RVRP($\mathcal P$), this route set is unique up to a reordering of the routes $\mathbf R_1,\dots,\mathbf R_m$, and $x$ and $\mathbf R$ attain the same transportation costs.
--
--   Here (3) is
--   $$
--   x_{ij}=1\iff\exists k\in K,\ \exists l\in\{0,\dots,n_k\}:\ (i,j)=(R_{k,l},R_{k,l+1}).
--   $$
--
--   The theorem reduces the distributionally robust chance-constrained CVRP, whose constraints range over possibly uncountably many distributions, to a deterministic two-index vehicle flow model that standard branch-and-cut schemes solve, whenever the ambiguity set yields a subadditive demand estimator.
--
--   **Formalization Note** The statement is the conjunction of Theorem 1 (i) and (ii). Finiteness of the worst-case VaR (the paper's $d_{\mathcal P}:2^{V_C}\to\mathbb R_+$) and $Q>0$ are explicit hypotheses because Lean's real supremum and division return $0$ on unbounded sets and zero denominators. Customers are 0-based and the depot is node `0 : Fin (n+1)`.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 722, Theorem 1

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_RCI_RouteSet
import Definitions.Def_DRCVRP_RCI_DemandEstimator
import Definitions.Def_DRCVRP_RCI_Formulations

open MeasureTheory

namespace DRCVRP.RCI

/-- Theorem 1, p. 722: if `q̃ ≥ 0` `ℙ`-a.s. for all `ℙ ∈ 𝒫` and `d_𝒫` satisfies the subadditivity
condition (S), then RVRP(𝒫) and 2VF(𝒫) are equivalent: (i) every RVRP(𝒫)-feasible route set
induces via (3) a 2VF(𝒫)-feasible `x` of the same cost; (ii) every 2VF(𝒫)-feasible `x` is
induced via (3) by an RVRP(𝒫)-feasible route set, unique up to reordering the routes, of the
same cost.
Standing hypotheses: costs `c(i,j) ≥ 0`, capacity `Q > 0`, `ε ∈ (0,1)`, every `ℙ ∈ 𝒫`
(`Amb`) a probability distribution with `q̃ ≥ 0` `ℙ`-a.s., the worst-case VaR of every customer
set finite (the paper's `d_𝒫` is real valued), and `d_𝒫` subadditive, condition (S). -/
theorem rvrp_equiv_twoIndexFlow {n m : ℕ} (c : Fin (n + 1) → Fin (n + 1) → ℝ) (hc : ∀ i j, 0 ≤ c i j)
    (Q : ℝ) (hQ : 0 < Q) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (Amb : Set (Measure (Fin n → ℝ))) (hAmb : ∀ P ∈ Amb, IsProbabilityMeasure P)
    (hnonneg : ∀ P ∈ Amb, ∀ᵐ q ∂P, ∀ i, 0 ≤ q i)
    (hbdd : ∀ S : Finset (Fin n), BddAbove ((fun P => MultistageStochastic.valueAtRisk P
      (fun q => ∑ i ∈ S, q i) (1 - ε)) '' Amb))
    (hsub : IsSubadditive Amb ε Q) :
    (∀ R : Fin m → List (Fin n), RVRPFeasible Amb ε Q R →
      TwoIndexFeasible Amb ε Q m (inducedFlow R) ∧ flowCost c (inducedFlow R) = routeSetCost c R) ∧
    (∀ x : Fin (n + 1) → Fin (n + 1) → ℕ, TwoIndexFeasible Amb ε Q m x →
      ∃ R : Fin m → List (Fin n), RVRPFeasible Amb ε Q R ∧ inducedFlow R = x ∧
        (∀ R' : Fin m → List (Fin n), IsRouteSet R' → inducedFlow R' = x →
          ∃ σ : Equiv.Perm (Fin m), R' = R ∘ σ) ∧
        flowCost c x = routeSetCost c R) := by sorry

end DRCVRP.RCI
