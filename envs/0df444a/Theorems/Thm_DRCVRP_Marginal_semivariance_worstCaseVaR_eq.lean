-- Prove2me | Theorems.Thm_DRCVRP_Marginal_semivariance_worstCaseVaR_eq
-- name    : DRCVRP.Marginal.semivariance_worstCaseVaR_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:40:31.223241+00:00
-- url     : https://prove2.me/theorems/b41b8576-f54e-4e55-ad09-21841f00535c
-- title:
--   Closed-form worst-case value-at-risk over marginalized semivariance ambiguity sets
-- statement:
--   Let $\mathcal P$ be a marginalized semivariance ambiguity set of the form (10),
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^n):\ \mathbb P[\tilde{\boldsymbol q}\in\mathcal Q]=1,\ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \mathbb E_{\mathbb P}\big[[\tilde q_i-\mu_i]_+^2\big]\le\sigma_i^+,\ \mathbb E_{\mathbb P}\big[[\mu_i-\tilde q_i]_+^2\big]\le\sigma_i^-\ \ \forall i\in V_C\Big\},
--   $$
--   where $[x]_+=\max\{x,0\}$, $\mathcal Q=[\underline{\boldsymbol q},\overline{\boldsymbol q}]$ with $\underline{\boldsymbol q}\ge\mathbf 0$, $\boldsymbol\mu\in\operatorname{int}\mathcal Q$, and $\boldsymbol\sigma^+,\boldsymbol\sigma^->\mathbf 0$. Let $\epsilon\in(0,1)$. Then for every customer $i$,
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}[\tilde q_i]=\mu_i+\min\Big\{\overline q_i-\mu_i,\ \frac{1-\epsilon}{\epsilon}(\mu_i-\underline q_i),\ \sqrt{\frac{\sigma_i^+}{\epsilon}},\ \frac{\sqrt{(1-\epsilon)\sigma_i^-}}{\epsilon}\Big\}.
--   $$
--
--   The last two terms come from the upper and the lower semivariance bound respectively. With Theorem 3 this gives the worst-case value-at-risk of every customer set over (10).
--
--   **Formalization Note** Customers are `Fin n` (0-based); the left side is `worstCaseVaR (semivarianceSet qlo qhi μ σplus σminus) ε {i}`. The four-term minimum is nested binary `min`. In the fourth term the root is taken of the product $(1-\epsilon)\sigma_i^-$ and the division by $\epsilon$ is outside it, as printed.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §4.3, p. 725, Proposition 4, Eq. (11) (ambiguity set Eq. (10))

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Marginal_WorstCaseVaR
import Definitions.Def_DRCVRP_Marginal_AmbiguitySets

open MeasureTheory

namespace DRCVRP.Marginal

/-- Proposition 4 (Ghosal and Wiesemann 2020, §4.3, p. 725, Eq. (11)): the worst-case
value-at-risk of one customer's demand over the marginalized semivariance ambiguity set (10). -/
theorem semivariance_worstCaseVaR_eq {n : ℕ}
    (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hqlo : ∀ i, 0 ≤ qlo i) (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (σplus σminus : Fin n → ℝ) (hσplus : ∀ i, 0 < σplus i) (hσminus : ∀ i, 0 < σminus i)
    (i : Fin n) :
    worstCaseVaR (semivarianceSet qlo qhi μ σplus σminus) ε {i} =
      μ i + min (min (min (qhi i - μ i) ((1 - ε) / ε * (μ i - qlo i)))
        (Real.sqrt (σplus i / ε))) (Real.sqrt ((1 - ε) * σminus i) / ε) := by sorry

end DRCVRP.Marginal
