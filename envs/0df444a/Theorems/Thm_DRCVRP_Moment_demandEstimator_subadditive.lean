-- Prove2me | Theorems.Thm_DRCVRP_Moment_demandEstimator_subadditive
-- name    : DRCVRP.Moment.demandEstimator_subadditive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:32:22.058934+00:00
-- url     : https://prove2.me/theorems/5849f34e-cb61-4dbe-baf9-03cb95379314
-- title:
--   Theorem 2 — the demand estimator $d_{\mathcal P}$ of a moment ambiguity set is subadditive
-- statement:
--   Let $\mathcal P$ be a moment ambiguity set of the form (4),
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^n):\ \mathbb P(\tilde{\boldsymbol q}\in\mathcal Q)=1,\ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \mathbb E_{\mathbb P}[\boldsymbol\varphi(\tilde{\boldsymbol q})]\le\boldsymbol\sigma\Big\},
--   $$
--   with support box $\mathcal Q=[\underline{\boldsymbol q},\overline{\boldsymbol q}]$, $\underline{\boldsymbol q}\ge\mathbf 0$, satisfying the standing assumptions $\boldsymbol\mu\in\operatorname{int}\mathcal Q$, each component $\varphi_l$ of $\boldsymbol\varphi:\mathbb R^n\to\mathbb R^p$ convex, and $\boldsymbol\varphi(\boldsymbol\mu)<\boldsymbol\sigma$. Let $\epsilon\in(0,1)$ be the risk level and $Q>0$ the vehicle capacity, and let
--   $$
--   d_{\mathcal P}(S)=\max\left\{\left\lceil\frac1Q\sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big]\right\rceil,1\right\}\ (S\neq\emptyset),\qquad d_{\mathcal P}(\emptyset)=0,
--   $$
--   be the demand estimator (2). Then $d_{\mathcal P}$ satisfies the paper's subadditivity condition "(S) Subadditivity. For all customer subsets $S, T\subseteq V_C$, we have $d_{\mathcal P}(S\cup T)\le d_{\mathcal P}(S)+d_{\mathcal P}(T)$":
--   $$
--   d_{\mathcal P}(S\cup T)\ \le\ d_{\mathcal P}(S)+d_{\mathcal P}(T)\qquad\text{for all } S,T\subseteq V_C .
--   $$
--
--   By Theorem 1 of the paper, subadditivity of $d_{\mathcal P}$ (together with nonnegative demands) makes the two-index vehicle flow formulation 2VF($\mathcal P$) equivalent to the route-based distributionally robust CVRP, so this theorem shows that for every moment ambiguity set the compact formulation can be solved by branch-and-cut in place of the route-based one. For marginal-histogram ambiguity sets the estimator can fail to be subadditive (Example 1 of the paper).
--
--   **Formalization Note** Customer subsets are `Finset (Fin n)` (overlapping and empty subsets included). The estimator is integer valued. The statement is about the rounded estimator with its ceiling and its $\max\{\cdot,1\}$, not about subadditivity of the worst-case VaR itself. See the definition item for the encoding of the ambiguity set and of the worst-case VaR.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 723, Theorem 2; condition (S) p. 722; estimator p. 721, Eq. (2); ambiguity set p. 722, Eq. (4) and standing assumptions

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Moment_AmbiguitySet

open MeasureTheory

namespace DRCVRP.Moment

theorem demandEstimator_subadditive {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (σ : Fin p → ℝ) (ε Q : ℝ)
    (hqlo : ∀ i, 0 ≤ qlo i)
    (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (hφ : ∀ l, ConvexOn ℝ Set.univ (φ l))
    (hσ : ∀ l, φ l μ < σ l)
    (hε0 : 0 < ε) (hε1 : ε < 1) (hQ : 0 < Q)
    (S T : Finset (Fin n)) :
    demandEstimator (momentAmbiguitySet qlo qhi μ φ σ) ε Q (S ∪ T) ≤
      demandEstimator (momentAmbiguitySet qlo qhi μ φ σ) ε Q S +
        demandEstimator (momentAmbiguitySet qlo qhi μ φ σ) ε Q T := by sorry

end DRCVRP.Moment
