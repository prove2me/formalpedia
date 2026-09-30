-- Prove2me | Theorems.Thm_DRCVRP_Marginal_worstCaseVaR_additive
-- name    : DRCVRP.Marginal.worstCaseVaR_additive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T02:38:39.691975+00:00
-- url     : https://prove2.me/theorems/a7130eb0-4de5-44e4-948d-5ed430e899ba
-- title:
--   Worst-case value-at-risk is additive over marginalized moment ambiguity sets
-- statement:
--   Let $\mathcal P$ be a marginalized moment ambiguity set of the form (5): for customers $V_C=\{1,\dots,n\}$, a support box $\mathcal Q=[\underline{\boldsymbol q},\overline{\boldsymbol q}]$ with $\underline{\boldsymbol q}\ge\mathbf 0$, a mean $\boldsymbol\mu\in\operatorname{int}\mathcal Q$, and for each customer $i$ a componentwise convex dispersion measure $\boldsymbol\varphi_i:\mathbb R\to\mathbb R^{p_i}$ and a bound $\boldsymbol\sigma_i\in\mathbb R^{p_i}$ with $\boldsymbol\varphi_i(\mu_i)<\boldsymbol\sigma_i$,
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^n):\ \mathbb P(\tilde{\boldsymbol q}\in\mathcal Q)=1,\ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \mathbb E_{\mathbb P}[\boldsymbol\varphi_i(\tilde q_i)]\le\boldsymbol\sigma_i\ \ \forall i\in V_C\Big\}.
--   $$
--   Let $\epsilon\in(0,1)$. Then for every nonempty customer subset $S\subseteq V_C$,
--   $$
--   \sup_{\mathbb P\in\mathcal P}\ \mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big]=\sum_{i\in S}\ \sup_{\mathbb P\in\mathcal P}\ \mathbb P\text{-VaR}_{1-\epsilon}[\tilde q_i].
--   $$
--
--   The value-at-risk of a sum is in general not the sum of the values-at-risk, even for single distributions in $\mathcal P$; the theorem says that the worst cases, taken separately for each side, agree. It reduces the distributionally robust vehicle routing problem over (5) to a deterministic one (Corollary 1) and makes the per-customer closed forms of Propositions 2–4 sufficient for every customer set.
--
--   **Formalization Note** Customers are `Fin n` (0-based), distributions are measures on `Fin n → ℝ`, and the worst-case value-at-risk is `worstCaseVaR (marginalSet qlo qhi μ φ σ) ε S`, a real supremum that is nonempty and bounded under the hypotheses. The standing assumptions of p. 723 are hypotheses: `0 ≤ qlo`, `qlo < μ < qhi` componentwise, each component `φ i l` convex on $\mathbb R$ (a real-valued convex function is continuous, so "closed" is automatic), and `φ i l (μ i) < σ i l`. The number of dispersion components `p i` may be any natural number.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §4, p. 723, Theorem 3 (ambiguity set Eq. (5))

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Marginal_WorstCaseVaR
import Definitions.Def_DRCVRP_Marginal_AmbiguitySets

open MeasureTheory

namespace DRCVRP.Marginal

/-- Theorem 3 (Ghosal and Wiesemann 2020, §4, p. 723): over every marginalized moment ambiguity
set (5), the worst-case value-at-risk of a total demand is the sum of the customers' worst-case
values-at-risk. -/
theorem worstCaseVaR_additive {n : ℕ}
    (qlo qhi μ : Fin n → ℝ) (ε : ℝ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hqlo : ∀ i, 0 ≤ qlo i) (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    {p : Fin n → ℕ} (φ : (i : Fin n) → Fin (p i) → ℝ → ℝ) (σ : (i : Fin n) → Fin (p i) → ℝ)
    (hφ : ∀ i l, ConvexOn ℝ Set.univ (φ i l)) (hσ : ∀ i l, φ i l (μ i) < σ i l)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    worstCaseVaR (marginalSet qlo qhi μ φ σ) ε S =
      ∑ i ∈ S, worstCaseVaR (marginalSet qlo qhi μ φ σ) ε {i} := by sorry

end DRCVRP.Marginal
