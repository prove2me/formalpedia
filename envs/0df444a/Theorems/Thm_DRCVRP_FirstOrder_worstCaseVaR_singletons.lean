-- Prove2me | Theorems.Thm_DRCVRP_FirstOrder_worstCaseVaR_singletons
-- name    : DRCVRP.FirstOrder.worstCaseVaR_singletons
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T03:08:00.972089+00:00
-- url     : https://prove2.me/theorems/a2d9c0f7-d76b-4a05-9a87-6a5379bf793a
-- title:
--   Corollary 3 — worst-case VaR for singleton blocks plus a total bound
-- statement:
--   Let $\mathcal P$ be the first-order generic moment ambiguity set with support $[\underline{\boldsymbol q},\overline{\boldsymbol q}]$, $\underline{\boldsymbol q}\ge\mathbf 0$, mean $\boldsymbol\mu$ with $\underline q_j<\mu_j<\overline q_j$ for all $j$, and bounds $\boldsymbol\nu>\mathbf 0$, and let $\epsilon\in(0,1)$. Suppose that $p=n+1$, $S_i=\{i\}$ for $i=1,\dots,n$, and $S_{n+1}=V_C$. Then for every customer subset $S\subseteq V_C$,
--
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}\Bigl[\sum_{i\in S}\tilde q_i\Bigr]=\mathbf 1_S^\top\boldsymbol\mu+\min\Bigl\{\frac{\nu_{n+1}}{2\epsilon},\ \sum_{i\in S}\min\Bigl\{\hat q_i,\ \frac{\nu_i}{2\epsilon}\Bigr\}\Bigr\},
--   $$
--
--   where $\hat{\boldsymbol q}=\min\{\overline{\boldsymbol q}-\boldsymbol\mu,\ \tfrac{1-\epsilon}{\epsilon}(\boldsymbol\mu-\underline{\boldsymbol q})\}$ componentwise.
--
--   Compared with the marginalized first-order ambiguity set, this set additionally bounds the sum of the mean absolute deviations of all customer demands; the worst-case value-at-risk remains in closed form.
--
--   **Formalization Note** Customers are `Fin n` and the $n+1$ subsets are indexed by `Fin (n+1)`: customer $i$'s singleton is `Sfam i.castSucc` and $S_{n+1}$ is `Sfam (Fin.last n)`.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, https://doi.org/10.1287/opre.2019.1924, §5.1, pp. 726–727, Corollary 3, Eq. (15)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_FirstOrder_AmbiguitySet
import Definitions.Def_DRCVRP_FirstOrder_ConvexProgram

open MeasureTheory

namespace DRCVRP.FirstOrder

/-- Corollary 3 (§5.1, pp. 726–727, Eq. (15)): with `p = n + 1`, `S_i = {i}` for every customer
`i` and `S_{n+1} = V_C`, the worst-case value-at-risk over (12) is
`1_Sᵀ μ + min {ν_{n+1}/(2ε), ∑_{i∈S} min {q̂_i, ν_i/(2ε)}}`. -/
theorem worstCaseVaR_singletons {n : ℕ} (qlo qhi μ : Fin n → ℝ)
    (Sfam : Fin (n + 1) → Finset (Fin n)) (ν : Fin (n + 1) → ℝ) (ε : ℝ)
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hν : ∀ l, 0 < ν l)
    (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hsing : ∀ i : Fin n, Sfam i.castSucc = {i})
    (hlast : Sfam (Fin.last n) = Finset.univ) (S : Finset (Fin n)) :
    worstCaseVaR (firstOrderAmbiguitySet qlo qhi μ Sfam ν) ε S =
      ∑ j ∈ S, μ j +
        min (ν (Fin.last n) / (2 * ε))
          (∑ i ∈ S, min (qhat qlo qhi μ ε i) (ν i.castSucc / (2 * ε))) := by sorry

end DRCVRP.FirstOrder
