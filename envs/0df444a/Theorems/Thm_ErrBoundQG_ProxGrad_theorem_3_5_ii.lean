-- Prove2me | Theorems.Thm_ErrBoundQG_ProxGrad_theorem_3_5_ii
-- name    : ErrBoundQG.ProxGrad.theorem_3_5_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:06.780042+00:00
-- url     : https://prove2.me/theorems/737b3916-b16e-4393-aeb9-5efb10f6c360
-- title:
--   Theorem 3.5, (3.11), p. 8 — for β-Lipschitz F, forward-backward and proximal point step lengths agree up to factors 1 ± βt
-- statement:
--   Let $G,\Phi:\mathbb R^n\rightrightarrows\mathbb R^n$ be maximal monotone operators with $\Phi(x) = F(x) + G(x)$ for a single-valued $F:\mathbb R^n\to\mathbb R^n$, and suppose $F$ is $\beta$-Lipschitz continuous, $\|F(x)-F(y)\|\le\beta\|x-y\|$, with $\beta\ge0$. Let $t>0$, let $\operatorname{prox}_{tG}=(I+tG)^{-1}$ and $\operatorname{prox}_{t\Phi}=(I+t\Phi)^{-1}$ be the resolvents, and $\mathcal G_t(x) = \frac1t\big(x-\operatorname{prox}_{tG}(x - tF(x))\big)$. Then for every $x\in\mathbb R^n$,
--   $$(1-\beta t)\,\|\mathcal G_t(x)\|\ \le\ \big\|t^{-1}\big(x - \operatorname{prox}_{t\Phi}(x)\big)\big\|\ \le\ (1+\beta t)\,\|\mathcal G_t(x)\|.$$
--
--   The step lengths of the forward-backward method and of the proximal point method on $\Phi$ are therefore proportional; this is the last step of the forward direction of Corollary 3.6.
--
--   **Formalization Note** The resolvents are maps $J_G$, $J_\Phi$ with $t^{-1}(x-J(x))\in G(J(x))$ (resp. $\Phi(J(x))$) for every $x$ (the published `IsResolvent`); for maximal monotone operators they exist and are unique. $\Phi(x) = F(x) + G(x)$ is the reading of "the difference $F := \Phi - G$ is single-valued".
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 8, Theorem 3.5, (3.11)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators

namespace ErrBoundQG.ProxGrad

theorem theorem_3_5_ii {n : ℕ} (G Φ : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hG : ThreeOpSplitting.Convergence.IsMaximalMonotone G)
    (hΦ : ThreeOpSplitting.Convergence.IsMaximalMonotone Φ)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x, Φ x = (fun w => F x + w) '' G x)
    (t : ℝ) (ht : 0 < t) (JG : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hJG : ThreeOpSplitting.Convergence.IsResolvent t G JG)
    (β : ℝ) (hβ : 0 ≤ β) (hFL : ∀ x y, ‖F x - F y‖ ≤ β * ‖x - y‖)
    (JΦ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hJΦ : ThreeOpSplitting.Convergence.IsResolvent t Φ JΦ) :
    ∀ x, (1 - β * t) * ‖t⁻¹ • (x - JG (x - t • F x))‖ ≤ ‖t⁻¹ • (x - JΦ x)‖ ∧
      ‖t⁻¹ • (x - JΦ x)‖ ≤ (1 + β * t) * ‖t⁻¹ • (x - JG (x - t • F x))‖ := by sorry

end ErrBoundQG.ProxGrad
