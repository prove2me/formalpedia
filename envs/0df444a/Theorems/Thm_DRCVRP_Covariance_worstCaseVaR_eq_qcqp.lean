-- Prove2me | Theorems.Thm_DRCVRP_Covariance_worstCaseVaR_eq_qcqp
-- name    : DRCVRP.Covariance.worstCaseVaR_eq_qcqp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T03:41:31.968762+00:00
-- url     : https://prove2.me/theorems/6890994a-a02f-4bf2-b637-9fb450bf954e
-- title:
--   Theorem 7 — worst-case VaR over a covariance ambiguity set is a quadratically constrained program
-- statement:
--   Let $\mathcal P$ be the covariance ambiguity set (16) with box $\mathcal Q=[\underline{\boldsymbol q},\overline{\boldsymbol q}]$, $\underline{\boldsymbol q}\ge\mathbf 0$, mean $\boldsymbol\mu\in\operatorname{int}\mathcal Q$ and covariance bound $\Sigma\succ0$, and let $\epsilon\in(0,1)$. For every customer subset $S\subseteq\{1,\dots,n\}$, the worst-case value-at-risk equals the optimal value of the convex quadratically constrained program (17):
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big]=\sup\Big\{\mathbf 1_S^\top\boldsymbol\mu+\mathbf 1_S^\top\boldsymbol q:\ \boldsymbol q^\top\Sigma^{-1}\boldsymbol q\le\frac{1-\epsilon}{\epsilon},\ \ \boldsymbol q\in[\boldsymbol q^\ell,\boldsymbol q^u]\Big\},
--   $$
--   where, componentwise,
--   $$
--   \boldsymbol q^\ell=\max\Big\{-\tfrac{1-\epsilon}{\epsilon}(\overline{\boldsymbol q}-\boldsymbol\mu),\ \underline{\boldsymbol q}-\boldsymbol\mu\Big\},\qquad\boldsymbol q^u=\min\Big\{\tfrac{1-\epsilon}{\epsilon}(\boldsymbol\mu-\underline{\boldsymbol q}),\ \overline{\boldsymbol q}-\boldsymbol\mu\Big\}.
--   $$
--   Here $\mathbf 1_S$ is the indicator vector of $S$: the objective sums over $S$ only, while the constraints involve all $n$ coordinates.
--
--   The program maximizes an affine function over the intersection of an ellipsoid and a box, so the worst-case value-at-risk — and with it the demand estimator in the rounded capacity inequalities of the distributionally robust vehicle routing problem — can be computed in polynomial time.
--
--   **Formalization Note** The paper's statement writes "$\mathbb P$-VaR" without a level; the level $1-\epsilon$, used in the sentence introducing the theorem and everywhere else in the paper, is read in. "The optimal objective value" of the maximization is stated as the supremum of the objective over the feasible set; the feasible set is compact and contains $\mathbf 0$, so the supremum is a maximum, but attainment is not part of the claim. `Sig⁻¹` is Mathlib's matrix inverse, the true inverse since $\Sigma\succ0$.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §5.2, p. 727, Theorem 7, Eq. (17)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Covariance_AmbiguitySet

open MeasureTheory Matrix

namespace DRCVRP.Covariance

/-- Theorem 7 (p. 727): over the covariance ambiguity set (16), the worst-case value-at-risk
`sup_{ℙ ∈ 𝒫} ℙ-VaR_{1-ε}[∑_{i ∈ S} q̃_i]` equals the optimal value of (17),
`maximize 1_Sᵀμ + 1_Sᵀq s.t. qᵀΣ⁻¹q ≤ (1-ε)/ε, q ∈ [q^ℓ, q^u]`. -/
theorem worstCaseVaR_eq_qcqp {n : ℕ} (qlo qhi μ : Fin n → ℝ) (Sig : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (S : Finset (Fin n))
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hSig : Sig.PosDef)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    worstCaseVaR (covarianceSet qlo qhi μ Sig) ε S =
      sSup ((fun q : Fin n → ℝ => ∑ j ∈ S, μ j + ∑ j ∈ S, q j) ''
        {q | q ⬝ᵥ (Sig⁻¹ *ᵥ q) ≤ (1 - ε) / ε ∧
          ∀ j, qLower qlo qhi μ ε j ≤ q j ∧ q j ≤ qUpper qlo qhi μ ε j}) := by sorry

end DRCVRP.Covariance
