-- Prove2me | Theorems.Thm_DRCVRP_Marginal_firstOrder_worstCaseVaR_eq
-- name    : DRCVRP.Marginal.firstOrder_worstCaseVaR_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:39:09.04982+00:00
-- url     : https://prove2.me/theorems/d42ee8f6-a477-405a-8427-3bca199c1082
-- title:
--   Closed-form worst-case value-at-risk over marginalized first-order ambiguity sets
-- statement:
--   Let $\mathcal P$ be a marginalized first-order ambiguity set of the form (6),
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^n):\ \mathbb P(\tilde{\boldsymbol q}\in\mathcal Q)=1,\ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \mathbb E_{\mathbb P}\big[|\tilde{\boldsymbol q}-\boldsymbol\mu|\big]\le\boldsymbol\sigma\Big\},
--   $$
--   where $\mathcal Q=[\underline{\boldsymbol q},\overline{\boldsymbol q}]$ with $\underline{\boldsymbol q}\ge\mathbf 0$, $\boldsymbol\mu\in\operatorname{int}\mathcal Q$ and $\boldsymbol\sigma>\mathbf 0$ (so $\sigma_i$ bounds the mean absolute deviation of customer $i$'s demand). Let $\epsilon\in(0,1)$. Then for every customer $i$,
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}[\tilde q_i]=\mu_i+\min\Big\{\overline q_i-\mu_i,\ \frac{1-\epsilon}{\epsilon}(\mu_i-\underline q_i),\ \frac1{2\epsilon}\sigma_i\Big\}.
--   $$
--
--   Together with Theorem 3 this gives the worst-case value-at-risk of every customer set over (6) in closed form. The supremum is in general not attained by any distribution in $\mathcal P$.
--
--   **Formalization Note** Customers are `Fin n` (0-based); the left side is `worstCaseVaR (firstOrderSet qlo qhi μ σ) ε {i}`, a real supremum over a nonempty bounded set. The three-term minimum is written as nested binary `min`.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §4.1, p. 724, Proposition 2, Eq. (7) (ambiguity set Eq. (6))

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Marginal_WorstCaseVaR
import Definitions.Def_DRCVRP_Marginal_AmbiguitySets

open MeasureTheory

namespace DRCVRP.Marginal

/-- Proposition 2 (Ghosal and Wiesemann 2020, §4.1, p. 724, Eq. (7)): the worst-case
value-at-risk of one customer's demand over the marginalized first-order ambiguity set (6). -/
theorem firstOrder_worstCaseVaR_eq {n : ℕ}
    (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hqlo : ∀ i, 0 ≤ qlo i) (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (σ : Fin n → ℝ) (hσ : ∀ i, 0 < σ i) (i : Fin n) :
    worstCaseVaR (firstOrderSet qlo qhi μ σ) ε {i} =
      μ i + min (min (qhi i - μ i) ((1 - ε) / ε * (μ i - qlo i))) (1 / (2 * ε) * σ i) := by sorry

end DRCVRP.Marginal
