-- Prove2me | Theorems.Thm_DRCVRP_FirstOrder_worstCaseVaR_disjoint_blocks
-- name    : DRCVRP.FirstOrder.worstCaseVaR_disjoint_blocks
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T03:05:09.889363+00:00
-- url     : https://prove2.me/theorems/7416442a-1dc2-4414-852f-6e2af4b79ca3
-- title:
--   Corollary 2 — worst-case VaR for disjoint blocks plus a total bound
-- statement:
--   Let $\mathcal P$ be the first-order generic moment ambiguity set with support $[\underline{\boldsymbol q},\overline{\boldsymbol q}]$, $\underline{\boldsymbol q}\ge\mathbf 0$, mean $\boldsymbol\mu$ with $\underline q_j<\mu_j<\overline q_j$ for all $j$, customer subsets $S_1,\dots,S_p$ and bounds $\boldsymbol\nu>\mathbf 0$, and let $\epsilon\in(0,1)$. Suppose that $S_1,\dots,S_{p-1}$ are pairwise disjoint with $\bigcup_{i=1}^{p-1}S_i=V_C$, and that $S_p=V_C$. Then for every customer subset $S\subseteq V_C$,
--
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}\Bigl[\sum_{i\in S}\tilde q_i\Bigr]=\mathbf 1_S^\top\boldsymbol\mu+\min\Bigl\{\frac{\nu_p}{2\epsilon},\ \sum_{i=1}^{p-1}\min\Bigl\{\mathbf 1_{S\cap S_i}^\top\hat{\boldsymbol q},\ \frac{\nu_i}{2\epsilon}\Bigr\}\Bigr\},
--   $$
--
--   where $\hat{\boldsymbol q}=\min\{\overline{\boldsymbol q}-\boldsymbol\mu,\ \tfrac{1-\epsilon}{\epsilon}(\boldsymbol\mu-\underline{\boldsymbol q})\}$ componentwise.
--
--   This is a closed-form special case of Theorem 5: mean-absolute-deviation bounds on non-overlapping groups of customers (for example municipalities) together with a bound on the total demand.
--
--   **Formalization Note** The number of subsets is written $p=r+1$; the paper's $S_1,\dots,S_{p-1}$ are `Sfam i.castSucc` for `i : Fin r` and $S_p$ is `Sfam (Fin.last r)`. Disjointness is required only among the first $r$ sets, as in the paper.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, https://doi.org/10.1287/opre.2019.1924, §5.1, p. 726, Corollary 2, Eq. (14)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_FirstOrder_AmbiguitySet
import Definitions.Def_DRCVRP_FirstOrder_ConvexProgram

open MeasureTheory

namespace DRCVRP.FirstOrder

/-- Corollary 2 (§5.1, p. 726, Eq. (14)): with `p = r + 1` subsets, the first `r` pairwise
disjoint and covering all customers and the last one equal to all customers, the worst-case
value-at-risk over (12) is `1_Sᵀ μ + min {ν_p/(2ε), ∑_{i<p} min {1_{S∩S_i}ᵀ q̂, ν_i/(2ε)}}`. -/
theorem worstCaseVaR_disjoint_blocks {n r : ℕ} (qlo qhi μ : Fin n → ℝ)
    (Sfam : Fin (r + 1) → Finset (Fin n)) (ν : Fin (r + 1) → ℝ) (ε : ℝ)
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hν : ∀ l, 0 < ν l)
    (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hdisj : ∀ i i' : Fin r, i ≠ i' → Disjoint (Sfam i.castSucc) (Sfam i'.castSucc))
    (hcover : ∀ c : Fin n, ∃ i : Fin r, c ∈ Sfam i.castSucc)
    (hlast : Sfam (Fin.last r) = Finset.univ) (S : Finset (Fin n)) :
    worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S =
      ∑ j ∈ S, μ j +
        min (ν (Fin.last r) / (2 * ε))
          (∑ i : Fin r,
            min (∑ j ∈ S ∩ Sfam i.castSucc, qhat qlo qhi μ ε j) (ν i.castSucc / (2 * ε))) := by sorry

end DRCVRP.FirstOrder
