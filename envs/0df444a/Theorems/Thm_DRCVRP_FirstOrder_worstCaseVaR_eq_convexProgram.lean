-- Prove2me | Theorems.Thm_DRCVRP_FirstOrder_worstCaseVaR_eq_convexProgram
-- name    : DRCVRP.FirstOrder.worstCaseVaR_eq_convexProgram
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T03:18:00.047312+00:00
-- url     : https://prove2.me/theorems/07699d8b-ea3d-4c82-aabb-144f309e339b
-- title:
--   Theorem 5 — worst-case VaR over first-order generic ambiguity sets equals the value of a convex program
-- statement:
--   Let $V_C=\{1,\dots,n\}$ be the customers, and let $\mathcal P$ be the first-order generic moment ambiguity set
--
--   $$
--   \mathcal P=\Bigl\{\mathbb P\in\mathcal P_0(\mathbb R^n):\mathbb P[\tilde{\boldsymbol q}\in[\underline{\boldsymbol q},\overline{\boldsymbol q}]]=1,\ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \mathbb E_{\mathbb P}[\mathbf 1_{S_i}^\top|\tilde{\boldsymbol q}-\boldsymbol\mu|]\le\nu_i\ \forall i=1,\dots,p\Bigr\}
--   $$
--
--   with $\underline{\boldsymbol q}\ge\mathbf 0$, $\underline q_j<\mu_j<\overline q_j$ for every customer $j$, arbitrary customer subsets $S_1,\dots,S_p\subseteq V_C$ (they may overlap and need not cover $V_C$) and $\boldsymbol\nu>\mathbf 0$. Let $\epsilon\in(0,1)$. Then for every customer subset $S\subseteq V_C$ the worst-case value-at-risk equals the optimal value of problem (13):
--
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}\Bigl[\sum_{i\in S}\tilde q_i\Bigr]=\inf_{\boldsymbol\gamma\in\mathbb R^p_+}\Bigl\{\mathbf 1_S^\top\boldsymbol\mu+\min\Bigl\{\overline{\boldsymbol q}-\boldsymbol\mu,\ \tfrac{1-\epsilon}{\epsilon}(\boldsymbol\mu-\underline{\boldsymbol q})\Bigr\}^\top\Bigl[\mathbf 1_S-2\sum_{i=1}^p\gamma_i\mathbf 1_{S_i}\Bigr]_+ +\frac1\epsilon\boldsymbol\nu^\top\boldsymbol\gamma\Bigr\},
--   $$
--
--   where the minimum and the positive part $[\cdot]_+$ are taken componentwise.
--
--   The worst-case value-at-risk over this set has no closed form in general, but the theorem expresses it as the value of a nonsmooth convex (linear-programmable) problem over the nonnegative orthant, so the demand estimator of the paper's branch-and-cut scheme can be computed in polynomial time.
--
--   **Formalization Note** "The optimal objective value" of the minimization is stated as the infimum of the objective over $\boldsymbol\gamma\ge\mathbf 0$; attainment is not part of the claim. Customers are `Fin n`, the subsets are `Sfam : Fin p → Finset (Fin n)`, and the worst-case value-at-risk is the real supremum of `MultistageStochastic.valueAtRisk` at level $1-\epsilon$ over the set.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, https://doi.org/10.1287/opre.2019.1924, §5.1, p. 726, Theorem 5, problem (13); ambiguity set (12), p. 725

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_FirstOrder_AmbiguitySet
import Definitions.Def_DRCVRP_FirstOrder_ConvexProgram

open MeasureTheory

namespace DRCVRP.FirstOrder

/-- Theorem 5 (§5.1, p. 726): over the first-order generic moment ambiguity set (12), the
worst-case value-at-risk of the cumulative demand of any customer subset `S` equals the optimal
value of problem (13), the infimum of its objective over `γ ∈ ℝ₊ᵖ`. -/
theorem worstCaseVaR_eq_convexProgram {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (Sfam : Fin p → Finset (Fin n)) (ν : Fin p → ℝ) (ε : ℝ)
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hν : ∀ l, 0 < ν l)
    (hε₀ : 0 < ε) (hε₁ : ε < 1) (S : Finset (Fin n)) :
    worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S =
      sInf (convexProgramObjective qlo qhi μ Sfam ν ε S '' {γ | ∀ l, 0 ≤ γ l}) := by sorry

end DRCVRP.FirstOrder
