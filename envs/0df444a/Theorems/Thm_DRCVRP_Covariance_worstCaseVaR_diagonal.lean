-- Prove2me | Theorems.Thm_DRCVRP_Covariance_worstCaseVaR_diagonal
-- name    : DRCVRP.Covariance.worstCaseVaR_diagonal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T03:33:32.771787+00:00
-- url     : https://prove2.me/theorems/80157ee8-2f3b-4c1f-a77f-b3aaa50c81a5
-- title:
--   Corollary 4 (corrected) — worst-case VaR for a diagonal covariance bound
-- statement:
--   Let $\mathcal P$ be the covariance ambiguity set (16) with box $[\underline{\boldsymbol q},\overline{\boldsymbol q}]$, $\underline{\boldsymbol q}\ge\mathbf 0$, mean $\boldsymbol\mu$ in the interior of the box, and diagonal covariance bound $\Sigma=\operatorname{diag}(\sigma_1^2,\dots,\sigma_n^2)$ with $\sigma_i>0$. Let $\epsilon\in(0,1)$, $r=\frac{1-\epsilon}{\epsilon}$, $\boldsymbol q^u=\min\{\frac{1-\epsilon}{\epsilon}(\boldsymbol\mu-\underline{\boldsymbol q}),\overline{\boldsymbol q}-\boldsymbol\mu\}$ componentwise, and for $\theta\ge0$ let $S(\theta)=\{i\in S:\sigma_i^2>\theta\,q^u_i\}$ and $s(\theta)=r-\sum_{i\in S(\theta)}(q^u_i/\sigma_i)^2$. Then for every customer subset $S$
--   $$
--   \sup_{\mathbb P\in\mathcal P}\mathbb P\text{-VaR}_{1-\epsilon}\Big[\sum_{i\in S}\tilde q_i\Big]=\sup_{\theta\in\Theta}\ \Big\{\mathbf 1_S^\top\boldsymbol\mu+\sum_{i\in S(\theta)}q^u_i+\sqrt{s(\theta)\sum_{i\in S\setminus S(\theta)}\sigma_i^2}\Big\},
--   $$
--   where $\Theta$ is the set of $\theta\ge0$ such that
--
--   1. $s(\theta)\ge0$ (the paper's restriction of the feasible region), and
--   2. $\sigma_i^2\sqrt{s(\theta)}\le q^u_i\sqrt{\sum_{k\in S\setminus S(\theta)}\sigma_k^2}$ for every $i\in S\setminus S(\theta)$.
--
--   Condition 2 says that the solution of (17) induced by $\theta$ — $q_i=q^u_i$ on $S(\theta)$, $q_i=\sigma_i^2\sqrt{s(\theta)}/\sqrt{\sum_{S\setminus S(\theta)}\sigma_k^2}$ on $S\setminus S(\theta)$, $q_i=0$ off $S$ — respects the upper bound $\boldsymbol q^u$. The result turns the quadratically constrained program of Theorem 7 into a one-parameter search, which the paper uses to evaluate the worst-case value-at-risk in time linear in $|S|$ once the ratios $q^u_i/\sigma_i^2$ are sorted.
--
--   **This is a corrected statement.** Corollary 4 as printed maximizes over all $\theta\ge0$ satisfying condition 1 only. That claim is false: for $n=1$, $S=\{1\}$, every large $\theta$ gives $S(\theta)=\emptyset$ and the value $\mu_1+\sigma_1\sqrt r$, whereas the worst-case value-at-risk is $\mu_1+\min\{q^u_1,\sigma_1\sqrt r\}$ (Theorem 7), which is smaller whenever $q^u_1<\sigma_1\sqrt r$; e.g. $\mu_1=1$, $\underline q_1=0$, $\overline q_1=1.2$, $\sigma_1=1$, $\epsilon=\frac12$ gives $2$ on the printed right-hand side, larger than $\overline q_1$, which bounds every value-at-risk. Condition 2 restores the equality: every $\theta\in\Theta$ induces a feasible point of (17), and the optimal solution of (17) is induced by some $\theta\in\Theta$.
--
--   **Formalization Note** As in Theorem 7, the paper writes "$\mathbb P$-VaR" without the level; the level $1-\epsilon$ used everywhere else in the paper is read in. Condition 2 is written without division so that it is meaningful when $S\setminus S(\theta)=\emptyset$ (then it is vacuous). The worst-case VaR and the program use the definitions `covarianceSet`, `worstCaseVaR`, `qUpper`, `capSet`, `capSlack`, `diagObjective`.
-- source:
--   Ghosal and Wiesemann, The Distributionally Robust Chance-Constrained Vehicle Routing Problem, Oper. Res. 68(3) (2020) 716–732, §5.2, p. 727, Corollary 4, Eq. (18) (corrected; the printed claim is false, see the statement)

import Mathlib
import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_DRCVRP_Covariance_AmbiguitySet
import Definitions.Def_DRCVRP_Covariance_DiagonalProgram

open MeasureTheory

namespace DRCVRP.Covariance

/-- Corollary 4 (p. 727), **corrected**. For the diagonal bound `Σ = diag(σ₁², …, σₙ²)`,
`σ_i > 0`, the worst-case value-at-risk equals the supremum of the objective of (18),
`1_Sᵀμ + ∑_{i ∈ S(θ)} q^u_i + √([(1-ε)/ε - ∑_{i ∈ S(θ)} (q^u_i/σ_i)²][∑_{i ∈ S∖S(θ)} σ_i²])`,
over the `θ ≥ 0` for which (a) the first factor under the root is nonnegative (the paper's
restriction) and (b) the induced deviations `σ_i² τ(θ)` of the customers `i ∈ S ∖ S(θ)`, where
`τ(θ) = √(slack) / √(∑_{S∖S(θ)} σ_k²)`, do not exceed `q^u_i`; (b) is written without division.
Condition (b) is the correction: as printed, without it, the claim fails already for `n = 1`,
where the supremum would be `μ₁ + σ₁√((1-ε)/ε)` even when this exceeds `q̄₁`. -/
theorem worstCaseVaR_diagonal {n : ℕ} (qlo qhi μ σ : Fin n → ℝ) (ε : ℝ) (S : Finset (Fin n))
    (hqlo : ∀ j, 0 ≤ qlo j) (hμ : ∀ j, qlo j < μ j ∧ μ j < qhi j) (hσ : ∀ i, 0 < σ i)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    worstCaseVaR (covarianceSet qlo qhi μ (Matrix.diagonal fun i => σ i ^ 2)) ε S =
      sSup ((fun θ : ℝ => ∑ j ∈ S, μ j +
          diagObjective (qUpper qlo qhi μ ε) σ S ((1 - ε) / ε) θ) ''
        {θ | 0 ≤ θ ∧ 0 ≤ capSlack (qUpper qlo qhi μ ε) σ S ((1 - ε) / ε) θ ∧
          ∀ i ∈ S \ capSet (qUpper qlo qhi μ ε) σ S θ,
            σ i ^ 2 * Real.sqrt (capSlack (qUpper qlo qhi μ ε) σ S ((1 - ε) / ε) θ) ≤
              qUpper qlo qhi μ ε i *
                Real.sqrt (∑ k ∈ S \ capSet (qUpper qlo qhi μ ε) σ S θ, σ k ^ 2)}) := by sorry

end DRCVRP.Covariance
