-- Prove2me | Theorems.Thm_DLevelNestedLogit_Pricing_stationary_point_iff
-- name    : DLevelNestedLogit.Pricing.stationary_point_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:47:26.177823+00:00
-- url     : https://prove2.me/theorems/59471cd8-2210-4127-8c27-7820df8e233d
-- title:
--   Corollary 7.2 — p is a stationary point of R_root iff p_l = 1/β_l + u_Parent(l)(p) for every product l
-- statement:
--   Consider the $d$-level nested logit price model under its standing assumptions ($\beta_l>0$, $\eta_j\in(0,1]$ for nonleaf $j\neq\mathrm{root}$, $\eta_{\mathrm{root}}=0$), with expected revenue $R_{\mathrm{root}}$ and scalars $u_j(\mathbf p)$ ($u_{\mathrm{root}}=R_{\mathrm{root}}$, $u_j=\eta_ju_{\mathrm{Parent}(j)}+(1-\eta_j)R_j$).
--
--   For every $\mathbf p\in\mathbb R^n_+$, $\mathbf p$ is a **stationary point** of $R_{\mathrm{root}}$, i.e. the gradient of $R_{\mathrm{root}}$ at $\mathbf p$ is zero, if and only if
--   $$
--   p_l=\frac1{\beta_l}+u_{\mathrm{Parent}(l)}(\mathbf p)\qquad\text{for all products }l .
--   $$
--
--   The condition turns stationarity into a fixed-point equation for the prices, which motivates the push-up-then-push-down algorithm.
--
--   **Formalization Note** "The gradient is zero" is `HasFDerivAt R_root 0 p`: $R_{\mathrm{root}}$ is Fréchet differentiable at $\mathbf p$ with zero derivative. This is the same notion of stationarity as in the goal theorem. $R_{\mathrm{root}}$ is defined on all of $\mathbb R^n$ and differentiated there (the paper defines stationarity by the unconstrained gradient; there is no boundary condition).
-- source:
--   Li, Rusmevichientong, Topaloglu, The d-Level Nested Logit Model: Assortment and Price Optimization Problems, Oper. Res. 63(2), 2015, p. 336, Corollary 7.2

import Mathlib
import Definitions.Def_DLevelNestedLogit_Pricing_Revenue

namespace DLevelNestedLogit.Pricing

/-- Corollary 7.2 (Li, Rusmevichientong, Topaloglu 2015, p. 336): for every `p ∈ ℝ^n_+`, `p` is
a stationary point of `R_root` (the gradient of `R_root` at `p` is zero) if and only if
`p_l = 1/β_l + u_{Parent(l)}(p)` for every product `l`. -/
theorem stationary_point_iff {n d : ℕ} (T : DLevelTree n d) (P : Params T)
    (hP : P.Standing) (p : Fin n → ℝ) (hp : ∀ l : Fin n, 0 ≤ p l) :
    HasFDerivAt (expectedRevenue P) (0 : (Fin n → ℝ) →L[ℝ] ℝ) p ↔
      ∀ l : Fin n, p l = 1 / P.β l + uScalar P p (T.parentOf l) := by sorry

end DLevelNestedLogit.Pricing
