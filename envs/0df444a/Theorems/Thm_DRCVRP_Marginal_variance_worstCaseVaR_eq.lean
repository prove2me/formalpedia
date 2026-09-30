-- Prove2me | Theorems.Thm_DRCVRP_Marginal_variance_worstCaseVaR_eq
-- name    : DRCVRP.Marginal.variance_worstCaseVaR_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:39:55.425013+00:00
-- url     : https://prove2.me/theorems/4a48f339-1f04-43f6-8c29-ecf940b24d7b
-- title:
--   Closed-form worst-case value-at-risk over marginalized variance ambiguity sets
-- statement:
--   Let $\mathcal P$ be a marginalized variance ambiguity set of the form (8),
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^n):\ \mathbb P[\tilde{\boldsymbol q}\in\mathcal Q]=1,\ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \mathbb E_{\mathbb P}\big[(\tilde q_i-\mu_i)^2\big]\le\sigma_i\ \ \forall i\in V_C\Big\},
--   $$
--   where $\mathcal Q=[\underline{\boldsymbol q},\overline{\boldsymbol q}]$ with $\underline{\boldsymbol q}\ge\mathbf 0$, $\boldsymbol\mu\in\operatorname{int}\mathcal Q$ and $\boldsymbol\sigma>\mathbf 0$ ($\sigma_i$ bounds the variance of customer $i$'s demand). Let $\epsilon\in(0,1)$. Then for every customer $i$,
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}[\tilde q_i]=\mu_i+\min\Big\{\overline q_i-\mu_i,\ \frac{1-\epsilon}{\epsilon}(\mu_i-\underline q_i),\ \sqrt{\frac{1-\epsilon}{\epsilon}\sigma_i}\Big\}.
--   $$
--
--   The last term is the sharp one-sided Chebyshev (Cantelli) bound; the first two account for the support. With Theorem 3 this gives the worst-case value-at-risk of every customer set over (8).
--
--   **Formalization Note** Customers are `Fin n` (0-based); the left side is `worstCaseVaR (varianceSet qlo qhi μ σ) ε {i}`. The three-term minimum is nested binary `min`; the square root is `Real.sqrt`, applied to a positive number here.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §4.2, p. 725, Proposition 3, Eq. (9) (ambiguity set Eq. (8))

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Marginal_WorstCaseVaR
import Definitions.Def_DRCVRP_Marginal_AmbiguitySets

open MeasureTheory

namespace DRCVRP.Marginal

/-- Proposition 3 (Ghosal and Wiesemann 2020, §4.2, p. 725, Eq. (9)): the worst-case
value-at-risk of one customer's demand over the marginalized variance ambiguity set (8). -/
theorem variance_worstCaseVaR_eq {n : ℕ}
    (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hqlo : ∀ i, 0 ≤ qlo i) (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i) (i : Fin n) :
    worstCaseVaR (varianceSet qlo qhi μ σ) ε {i} =
      μ i + min (min (qhi i - μ i) ((1 - ε) / ε * (μ i - qlo i)))
        (Real.sqrt ((1 - ε) / ε * σ i)) := by sorry

end DRCVRP.Marginal
