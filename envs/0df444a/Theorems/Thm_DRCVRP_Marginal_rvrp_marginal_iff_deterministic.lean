-- Prove2me | Theorems.Thm_DRCVRP_Marginal_rvrp_marginal_iff_deterministic
-- name    : DRCVRP.Marginal.rvrp_marginal_iff_deterministic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:41:31.796244+00:00
-- url     : https://prove2.me/theorems/6fd7c5a4-1475-4211-98a8-c6118c28ab99
-- title:
--   The distributionally robust CVRP over a marginalized moment set is a deterministic CVRP
-- statement:
--   Let $\mathcal P$ be a marginalized moment ambiguity set of the form (5) under the standing assumptions ($\underline{\boldsymbol q}\ge\mathbf 0$, $\boldsymbol\mu\in\operatorname{int}\mathcal Q$, componentwise convex $\boldsymbol\varphi_i$ with $\boldsymbol\varphi_i(\mu_i)<\boldsymbol\sigma_i$), let $\epsilon\in(0,1)$ and let the vehicle capacity be $Q\ge0$. Define the deterministic demands
--   $$
--   q_i=\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}[\tilde q_i],\qquad i\in V_C.
--   $$
--   Then for every assignment $\mathbf R=(R_1,\dots,R_m)$ of ordered customer lists to the $m$ vehicles,
--   $$
--   \mathbf R \text{ is feasible in RVRP}(\mathcal P)\iff \mathbf R\text{ is feasible in the deterministic CVRP with demands }\boldsymbol q .
--   $$
--   Here RVRP($\mathcal P$)-feasibility means $\mathbf R\in\mathfrak P(V_C,m)$ and $\mathbb P[\sum_{i\in R_k}\tilde q_i\le Q]\ge1-\epsilon$ for all $\mathbb P\in\mathcal P$ and all $k$; deterministic feasibility means $\mathbf R\in\mathfrak P(V_C,m)$ and $\sum_{i\in R_k}q_i\le Q$ for all $k$.
--
--   Both problems minimize the same transportation cost $c(\mathbf R)$, so equality of their feasible sets is the paper's statement that the distributionally robust CVRP over (5) is equivalent to the deterministic CVRP with these demands. It allows any deterministic CVRP solver to be used for the robust problem.
--
--   **Formalization Note** Customers are `Fin n` (0-based), vehicles `Fin m`, routes `List (Fin n)`; `RVRPFeasible` and `CVRPFeasible` both include the route-set condition $\mathbf R\in\mathfrak P(V_C,m)$. The demand of customer `i` is `worstCaseVaR (marginalSet qlo qhi μ φ σ) ε {i}`. The capacity is only assumed nonnegative ($Q\in\mathbb R_+$, p. 718).
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §4, p. 723, Corollary 1 (ambiguity set Eq. (5); route sets, deterministic CVRP and RVRP(𝒫) from §2, pp. 718–719)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Marginal_WorstCaseVaR
import Definitions.Def_DRCVRP_Marginal_AmbiguitySets
import Definitions.Def_DRCVRP_Marginal_Routing

open MeasureTheory

namespace DRCVRP.Marginal

/-- Corollary 1 (Ghosal and Wiesemann 2020, §4, p. 723): over a marginalized moment ambiguity
set (5), a route set is feasible in RVRP(𝒫) if and only if it is feasible in the deterministic
CVRP with customer demands `q_i = sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[q̃_i]`. Both problems minimize the same
cost `c(R)`, so they are equivalent. -/
theorem rvrp_marginal_iff_deterministic {n m : ℕ}
    (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hqlo : ∀ i, 0 ≤ qlo i) (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    {p : Fin n → ℕ} (φ : (i : Fin n) → Fin (p i) → ℝ → ℝ) (σ : (i : Fin n) → Fin (p i) → ℝ)
    (hφ : ∀ i l, ConvexOn ℝ Set.univ (φ i l)) (hσ : ∀ i l, φ i l (μ i) < σ i l)
    (Q : ℝ) (hQ : 0 ≤ Q) (R : Fin m → List (Fin n)) :
    RVRPFeasible (marginalSet qlo qhi μ φ σ) ε Q R ↔
      CVRPFeasible (fun i => worstCaseVaR (marginalSet qlo qhi μ φ σ) ε {i}) Q R := by sorry

end DRCVRP.Marginal
