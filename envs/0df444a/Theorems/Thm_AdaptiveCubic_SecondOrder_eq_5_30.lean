-- Prove2me | Theorems.Thm_AdaptiveCubic_SecondOrder_eq_5_30
-- name    : AdaptiveCubic.SecondOrder.eq_5_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:20.83275+00:00
-- url     : https://prove2.me/theorems/cf4da532-f708-4225-b62b-7c3415883c53
-- title:
--   (5.30) — at most L^s_2 = ⌈κ_curv ε^(−3)⌉ successful iterations with negative curvature
-- statement:
--   Under the hypotheses of (5.29), and with $f(x_k)\ge f_{\rm low}$ for all $k$, let
--
--   $$\kappa_{\rm curv}=\frac{f(x_0)-f_{\rm low}}{\eta_1\alpha_{\rm curv}},\qquad \alpha_{\rm curv}=\frac{\sigma_{\min}}{6L_0^3}, \qquad (5.26)$$
--
--   and let $\mathcal S^\epsilon_\lambda=\{k\in\mathcal S: -\lambda_{\min}(Q_k^\top B_kQ_k)>\epsilon\}$ be the set of successful iterations with negative curvature. Then $\mathcal S^\epsilon_\lambda$ is finite and
--
--   $$|\mathcal S^\epsilon_\lambda|\ \le\ L^s_2 := \left\lceil \kappa_{\rm curv}\,\epsilon^{-3}\right\rceil. \qquad (5.30)$$
--
--   This is the first part of Corollary 5.4, obtained from Theorem 2.2 with $F_k=|\lambda_{\min}(Q_k^\top B_kQ_k)|$ and $p=3$.
--
--   **Formalization Note** AF.4 is not used and is omitted; the goal theorem keeps it.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 16, proof of Corollary 5.4, (5.30); (5.25), (5.26)

import Mathlib
import Definitions.Def_AdaptiveCubic_SecondOrder_IsARCSRun
import Definitions.Def_AdaptiveCubic_SecondOrder_lamMin

open scoped RealInnerProductSpace

namespace AdaptiveCubic.SecondOrder

/-- Proof of Corollary 5.4, (5.30), p. 16 (Cartis, Gould & Toint, ARC Part II, preprint rev.
15 Sep 2009). The set `S^ε_λ = {k ∈ S : −λ_min(Q_kᵀB_kQ_k) > ε}` of successful iterations with
negative curvature is finite and `|S^ε_λ| ≤ L^s_2 = ⌈κ_curv ε^{−3}⌉` (5.25).
Notation: `S` is the set of successful iterations (`ρ_k ≥ η₁`, (2.8)), `λ_k = λ_min(Q_kᵀB_kQ_k)` is
`lamMin (B k) (Lsub k)` for the subspace `L_k` = `Lsub k`, `L₀ = max(σ₀, (3/2)γ₂(C + L))` (5.4),
`α_curv = σ_min/(6L₀³)` and `κ_curv = (f(x₀) − f_low)/(η₁α_curv)` (5.26). Hypotheses: ARC(S) run
(Algorithm 4.1), AF.3, AF.6, AM.4 with `H = fderiv ℝ (gradient f)`, (2.11), (2.6) for all `k`
(p. 12, last paragraph of §4), `s_k` a global minimizer of `m_k` over `L_k`. Also `f(x_k) ≥ f_low` for all `k`. -/
theorem eq_5_30 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ κθ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCSRun f γ₁ γ₂ η₁ η₂ κθ x s σ B)
    (hAF3 : ContDiff ℝ 2 f)
    (L : ℝ) (hL : 0 < L)
    (hAF6 : ∀ y z, ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) z‖ ≤ L * ‖y - z‖)
    (C : ℝ) (hC : 0 < C)
    (hAM4 : ∀ k, ‖(fderiv ℝ (gradient f) (x k) - B k) (s k)‖ ≤ C * ‖s k‖ ^ 2)
    (flow : ℝ) (hflow : ∀ k, flow ≤ f (x k))
    (σmin : ℝ) (hσmin : 0 < σmin) (h211 : ∀ k, σmin ≤ σ k)
    (h26 : ∀ k, AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) < f (x k))
    (Lsub : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hsL : ∀ k, s k ∈ Lsub k)
    (hmin : ∀ k, ∀ t ∈ Lsub k,
      AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) ≤ AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) t)
    (ε : ℝ) (hε : 0 < ε) :
    let L₀ := max (σ 0) (3 / 2 * γ₂ * (C + L))
    let αcurv := σmin / (6 * L₀ ^ 3)
    let κcurv := (f (x 0) - flow) / (η₁ * αcurv)
    ({k | η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧ ε < -lamMin (B k) (Lsub k)}).Finite ∧
      (({k | η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧ ε < -lamMin (B k) (Lsub k)}).ncard : ℤ) ≤
        ⌈κcurv * ε ^ (-3 : ℤ)⌉ := by sorry

end AdaptiveCubic.SecondOrder
