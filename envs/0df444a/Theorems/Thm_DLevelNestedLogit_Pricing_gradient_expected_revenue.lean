-- Prove2me | Theorems.Thm_DLevelNestedLogit_Pricing_gradient_expected_revenue
-- name    : DLevelNestedLogit.Pricing.gradient_expected_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T05:47:29.927644+00:00
-- url     : https://prove2.me/theorems/88c10c4c-6833-42f8-b191-8ad1ea3c5f1f
-- title:
--   Lemma 7.1 — gradient of the expected revenue: ∂R_root/∂p_l = −θ_l β_l (p_l − 1/β_l − u_Parent(l))
-- statement:
--   Consider the $d$-level nested logit price model under its standing assumptions ($\beta_l>0$, $\eta_j\in(0,1]$ for nonleaf $j\neq\mathrm{root}$, $\eta_{\mathrm{root}}=0$). Let $R_{\mathrm{root}}(\mathbf p)$ be the expected revenue of the price vector $\mathbf p$, $\theta_l(\mathbf p)$ the probability that a customer chooses product $l$, and $u_j(\mathbf p)$ the scalars defined by $u_{\mathrm{root}}=R_{\mathrm{root}}$ and $u_j=\eta_ju_{\mathrm{Parent}(j)}+(1-\eta_j)R_j$.
--
--   For every price vector $\mathbf p\in\mathbb R^n_+$ and every product $l$, the expected revenue is differentiable in $p_l$ at $\mathbf p$ and
--   $$
--   \frac{\partial R_{\mathrm{root}}}{\partial p_l}(\mathbf p)=-\theta_l(\mathbf p)\,\beta_l\Big(p_l-\frac1{\beta_l}-u_{\mathrm{Parent}(l)}(\mathbf p)\Big).
--   $$
--
--   The lemma gives the gradient in closed form from one bottom-up and one top-down pass over the tree, and is the basis of the stationarity characterization (Corollary 7.2).
--
--   **Formalization Note** The partial derivative is expressed as `HasDerivAt` of the one-variable function $x\mapsto R_{\mathrm{root}}(\mathbf p$ with $p_l$ replaced by $x)$ at $x=p_l$, which asserts both differentiability and the value. $R_{\mathrm{root}}$ is defined on all of $\mathbb R^n$, so the derivative is two-sided even when $p_l=0$; the hypothesis $\mathbf p\in\mathbb R^n_+$ is kept as printed. Product $l$ is `l : Fin n`.
-- source:
--   Li, Rusmevichientong, Topaloglu, The d-Level Nested Logit Model: Assortment and Price Optimization Problems, Oper. Res. 63(2), 2015, p. 335, Lemma 7.1

import Mathlib
import Definitions.Def_DLevelNestedLogit_Pricing_Revenue

namespace DLevelNestedLogit.Pricing

/-- Lemma 7.1 (Li, Rusmevichientong, Topaloglu 2015, p. 335): for every `p ∈ ℝ^n_+` and every
product `l`, `∂R_root/∂p_l (p) = −θ_l(p) β_l (p_l − 1/β_l − u_{Parent(l)}(p))`. -/
theorem gradient_expected_revenue {n d : ℕ} (T : DLevelTree n d) (P : Params T)
    (hP : P.Standing) (p : Fin n → ℝ) (hp : ∀ l : Fin n, 0 ≤ p l) (l : Fin n) :
    HasDerivAt (fun x : ℝ => expectedRevenue P (Function.update p l x))
      (-(choiceProb P p l) * P.β l * (p l - 1 / P.β l - uScalar P p (T.parentOf l))) (p l) := by sorry

end DLevelNestedLogit.Pricing
