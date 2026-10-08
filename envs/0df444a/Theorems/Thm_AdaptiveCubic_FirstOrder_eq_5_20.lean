-- Prove2me | Theorems.Thm_AdaptiveCubic_FirstOrder_eq_5_20
-- name    : AdaptiveCubic.FirstOrder.eq_5_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:40:50.670986+00:00
-- url     : https://prove2.me/theorems/a69862ef-8023-477c-9a67-8e59480df04f
-- title:
--   Proof of Corollary 5.3, (5.20) — model decrease α_S ε^(3/2) on S^ε_g
-- statement:
--   Consider a run of ARC(S) (Algorithm 4.1) on $f$ under AF.3 ($f\in C^2$), AF.4 (gradient $\kappa_H$-Lipschitz on an open convex set containing the iterates, $\kappa_H\ge1$), AF.6 (Hessian $L$-Lipschitz on $\mathbb R^n$, $L>0$), AM.4 ($\|(H(x_k)-B_k)s_k\|\le C\|s_k\|^2$, $C>0$), (2.11) ($\sigma_k\ge\sigma_{\min}>0$) and (2.6) ($m_k(s_k)<f(x_k)$ for all $k$). Let $\epsilon>0$ and let
--
--   $$\mathcal S^\epsilon_g=\{k\in\mathcal S:\ \min(\|g_k\|,\|g_{k+1}\|)>\epsilon\}$$
--
--   be the successful iterations at which both the current and the next gradient exceed $\epsilon$ (5.19). Then
--
--   $$f(x_k)-m_k(s_k)\ge\alpha_S\,\epsilon^{3/2}\quad\text{for all }k\in\mathcal S^\epsilon_g,\qquad \alpha_S=\frac{\sigma_{\min}\kappa_g^3}{6},$$
--
--   where $\kappa_g=\sqrt{(1-\kappa_\theta)/(\tfrac12L+C+L_0+\kappa_\theta\kappa_H)}$ (5.6) and $L_0=\max(\sigma_0,\tfrac32\gamma_2(C+L))$ (5.4).
--
--   This is hypothesis (2.18) of Theorem 2.2 with $p=3/2$ and $F_k=\min(\|g_k\|,\|g_{k+1}\|)$, the step that produces the $\epsilon^{-3/2}$ count.
--
--   **Formalization Note** $\epsilon^{3/2}$ is the real power `ε ^ (3 / 2 : ℝ)`. The constants are written out with `let` in the statement. (2.6) for all $k$ is the paper's standing assumption for ARC(S) (p. 12, last paragraph of §4).
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 15, proof of Corollary 5.3, (5.19)–(5.20); p. 14, (5.16)

import Mathlib
import Definitions.Def_AdaptiveCubic_FirstOrder_IsARCSRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.FirstOrder

/-- Proof of Corollary 5.3, (5.20), p. 15 (Cartis, Gould & Toint, ARC Part II, preprint rev.
15 Sep 2009).
Standing hypotheses: a run of ARC(S) (Algorithm 4.1, p. 12: Algorithm 2.1 with (4.1), (4.2),
TC.s (4.7) and (2.2)); AF.3 `f ∈ C²(ℝⁿ)` (5.1); AF.4 `‖g(y) − g(z)‖ ≤ κ_H‖y − z‖` on an open
convex `X` containing all iterates, `κ_H ≥ 1` (3.2); AF.6 `‖H(y) − H(z)‖ ≤ L‖y − z‖` for all
`y, z`, `L > 0` (5.2); AM.4 `‖(H(x_k) − B_k)s_k‖ ≤ C‖s_k‖²`, `C > 0` (5.3); (2.11)
`σ_k ≥ σ_min > 0`; and (2.6) `m_k(s_k) < f(x_k)` for all `k`, the standing assumption for ARC(S)
(p. 12, last paragraph of §4; p. 4). Here `g = ∇f`, `H = ∇²f = fderiv ℝ (gradient f)`.
Then `f(x_k) − m_k(s_k) ≥ α_S ε^{3/2}` for every `k ∈ S^ε_g`, the successful iterations with
`min(‖g_k‖, ‖g_{k+1}‖) > ε` (5.19), where `α_S = σ_min κ_g³/6` (5.16), `κ_g` is (5.6) and
`L₀` is (5.4). -/
theorem eq_5_20 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ κθ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCSRun f γ₁ γ₂ η₁ η₂ κθ x s σ B)
    (hAF3 : ContDiff ℝ 2 f)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXo : IsOpen X) (hXc : Convex ℝ X)
    (hxX : ∀ k, x k ∈ X) (κH : ℝ) (hκH : 1 ≤ κH)
    (hAF4 : ∀ y ∈ X, ∀ z ∈ X, ‖gradient f y - gradient f z‖ ≤ κH * ‖y - z‖)
    (L : ℝ) (hL : 0 < L)
    (hAF6 : ∀ y z, ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) z‖ ≤ L * ‖y - z‖)
    (C : ℝ) (hC : 0 < C)
    (hAM4 : ∀ k, ‖(fderiv ℝ (gradient f) (x k) - B k) (s k)‖ ≤ C * ‖s k‖ ^ 2)
    (h26 : ∀ k, AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) < f (x k))
    (σmin : ℝ) (hσmin : 0 < σmin) (h211 : ∀ k, σmin ≤ σ k)
    (ε : ℝ) (hε : 0 < ε) :
    let L₀ := max (σ 0) (3 / 2 * γ₂ * (C + L))
    let κg := Real.sqrt ((1 - κθ) / (1 / 2 * L + C + L₀ + κθ * κH))
    let αS := σmin * κg ^ 3 / 6
    ∀ k, η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) →
      ε < min ‖gradient f (x k)‖ ‖gradient f (x (k + 1))‖ →
      αS * ε ^ (3 / 2 : ℝ) ≤ f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) := by sorry

end AdaptiveCubic.FirstOrder
