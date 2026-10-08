-- Prove2me | Theorems.Thm_DRCVRP_Moment_twoPoint_tendsto_worstCaseVaR
-- name    : DRCVRP.Moment.twoPoint_tendsto_worstCaseVaR
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T02:27:00.421999+00:00
-- url     : https://prove2.me/theorems/ffa9c67b-e050-4b08-8afb-89b81f851c47
-- title:
--   Proposition 1 — two-point distributions attain the worst-case VaR over a moment ambiguity set asymptotically
-- statement:
--   Let $\mathcal P$ be a moment ambiguity set of the form (4),
--   $$
--   \mathcal P=\Big\{\mathbb P\in\mathcal P_0(\mathbb R^n):\ \mathbb P(\tilde{\boldsymbol q}\in\mathcal Q)=1,\ \mathbb E_{\mathbb P}[\tilde{\boldsymbol q}]=\boldsymbol\mu,\ \mathbb E_{\mathbb P}[\boldsymbol\varphi(\tilde{\boldsymbol q})]\le\boldsymbol\sigma\Big\},
--   $$
--   with support box $\mathcal Q=[\underline{\boldsymbol q},\overline{\boldsymbol q}]$, $\underline{\boldsymbol q}\ge\mathbf 0$, satisfying the paper's standing assumptions: $\boldsymbol\mu\in\operatorname{int}\mathcal Q$ (i.e. $\underline q_i<\mu_i<\overline q_i$ for every $i$), each component $\varphi_l$ of the dispersion measure $\boldsymbol\varphi:\mathbb R^n\to\mathbb R^p$ is convex, and $\boldsymbol\varphi(\boldsymbol\mu)<\boldsymbol\sigma$ componentwise. Let $\epsilon\in(0,1)$.
--
--   Then for every customer subset $S\subseteq V_C$ there are two-point distributions
--   $$
--   \mathbb P^t=p_1^t\cdot\delta_{\boldsymbol q_1^t}+p_2^t\cdot\delta_{\boldsymbol q_2^t}\in\mathcal P,\qquad p_1^t,p_2^t\in\mathbb R_+,\quad \boldsymbol q_1^t,\boldsymbol q_2^t\in\mathcal Q,\qquad t=0,1,2,\dots,
--   $$
--   such that
--   $$
--   \mathbb P^t\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big]\ \longrightarrow\ \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big]\qquad\text{as }t\to\infty.
--   $$
--
--   The worst-case value-at-risk over a moment ambiguity set is thus asymptotically attained by distributions with only two demand scenarios, however many moment constraints the set contains. The supremum need not be attained.
--
--   **Formalization Note** The sequences are indexed by `t : ℕ`. Membership in the ambiguity set forces $p_1^t+p_2^t=1$, so that is not stated separately; the two points may coincide. See the definition item for the encoding of the ambiguity set, the value-at-risk (published `MultistageStochastic.valueAtRisk` at level $1-\epsilon$) and the worst-case VaR (a real supremum, which is the true supremum because the set of VaRs is nonempty and bounded). "Closed" in the standing assumptions is automatic for a real-valued convex function and is not a separate hypothesis.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §3, p. 723, Proposition 1; ambiguity set p. 722, Eq. (4) and the standing assumptions stated below it

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Moment_AmbiguitySet

open MeasureTheory Filter Topology

namespace DRCVRP.Moment

theorem twoPoint_tendsto_worstCaseVaR {n p : ℕ} (qlo qhi μ : Fin n → ℝ)
    (φ : Fin p → (Fin n → ℝ) → ℝ) (σ : Fin p → ℝ) (ε : ℝ)
    (hqlo : ∀ i, 0 ≤ qlo i)
    (hμ : ∀ i, qlo i < μ i ∧ μ i < qhi i)
    (hφ : ∀ l, ConvexOn ℝ Set.univ (φ l))
    (hσ : ∀ l, φ l μ < σ l)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (S : Finset (Fin n)) :
    ∃ (p₁ p₂ : ℕ → ℝ) (q₁ q₂ : ℕ → Fin n → ℝ),
      (∀ t, 0 ≤ p₁ t ∧ 0 ≤ p₂ t ∧ q₁ t ∈ Set.Icc qlo qhi ∧ q₂ t ∈ Set.Icc qlo qhi ∧
        twoPointMeasure (p₁ t) (p₂ t) (q₁ t) (q₂ t) ∈ momentAmbiguitySet qlo qhi μ φ σ) ∧
      Tendsto
        (fun t => MultistageStochastic.valueAtRisk (twoPointMeasure (p₁ t) (p₂ t) (q₁ t) (q₂ t))
          (fun q => ∑ i ∈ S, q i) (1 - ε))
        atTop (𝓝 (worstCaseVaR (momentAmbiguitySet qlo qhi μ φ σ) ε S)) := by sorry

end DRCVRP.Moment
