-- Prove2me | Theorems.Thm_AdaptiveCubic_SecondOrder_eq_5_29
-- name    : AdaptiveCubic.SecondOrder.eq_5_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:35.470979+00:00
-- url     : https://prove2.me/theorems/20b4f0a8-5082-4cf8-ada6-00e70600e233
-- title:
--   (5.29) — model decrease α_curv ε³ at every iteration with negative curvature
-- statement:
--   Consider a run of ARC(S) on $f$ under AF.3, AF.6 and AM.4 (constants $L, C>0$), with $\sigma_k\ge\sigma_{\min}>0$ (2.11) and $m_k(s_k)<f(x_k)$ (2.6) for all $k$, in which each step $s_k$ is a global minimizer of $m_k$ over a subspace $\mathcal L_k$ spanned by the orthonormal columns of $Q_k$. Let $\epsilon>0$, $L_0=\max(\sigma_0,\tfrac32\gamma_2(C+L))$ (5.4) and
--
--   $$\alpha_{\rm curv}=\frac{\sigma_{\min}}{6L_0^3}. \qquad (5.26)$$
--
--   Then
--
--   $$f(x_k)-m_k(s_k)\ \ge\ \alpha_{\rm curv}\,\epsilon^3 \quad\text{for all } k\ge0 \text{ with } -\lambda_{\min}(Q_k^\top B_kQ_k)>\epsilon,$$
--
--   whether or not iteration $k$ is successful. This is hypothesis (2.18) of Theorem 2.2 with $p=3$ for the curvature measure.
--
--   **Formalization Note** $H=$ `fderiv ℝ (gradient f)`; (2.6) is assumed for all $k$ (p. 12, last paragraph of §4). AF.4, TC.s and the lower bound $f_{\rm low}$, hypotheses of Corollary 5.4, are not used by this step and are omitted here.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 16, proof of Corollary 5.4, (5.29); (5.26)

import Mathlib
import Definitions.Def_AdaptiveCubic_SecondOrder_IsARCSRun
import Definitions.Def_AdaptiveCubic_SecondOrder_lamMin

open scoped RealInnerProductSpace

namespace AdaptiveCubic.SecondOrder

/-- Proof of Corollary 5.4, (5.29), p. 16 (Cartis, Gould & Toint, ARC Part II, preprint rev.
15 Sep 2009). `f(x_k) − m_k(s_k) ≥ α_curv ε³` for all `k ≥ 0` with `−λ_min(Q_kᵀB_kQ_k) > ε`
(successful or not), where `α_curv = σ_min/(6L₀³)` (5.26) and `L₀ = max(σ₀, (3/2)γ₂(C + L))` (5.4).
Notation: `S` is the set of successful iterations (`ρ_k ≥ η₁`, (2.8)), `λ_k = λ_min(Q_kᵀB_kQ_k)` is
`lamMin (B k) (Lsub k)` for the subspace `L_k` = `Lsub k`, `L₀ = max(σ₀, (3/2)γ₂(C + L))` (5.4),
`α_curv = σ_min/(6L₀³)` and `κ_curv = (f(x₀) − f_low)/(η₁α_curv)` (5.26). Hypotheses: ARC(S) run
(Algorithm 4.1), AF.3, AF.6, AM.4 with `H = fderiv ℝ (gradient f)`, (2.11), (2.6) for all `k`
(p. 12, last paragraph of §4), `s_k` a global minimizer of `m_k` over `L_k`. -/
theorem eq_5_29 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ κθ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCSRun f γ₁ γ₂ η₁ η₂ κθ x s σ B)
    (hAF3 : ContDiff ℝ 2 f)
    (L : ℝ) (hL : 0 < L)
    (hAF6 : ∀ y z, ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) z‖ ≤ L * ‖y - z‖)
    (C : ℝ) (hC : 0 < C)
    (hAM4 : ∀ k, ‖(fderiv ℝ (gradient f) (x k) - B k) (s k)‖ ≤ C * ‖s k‖ ^ 2)
    (σmin : ℝ) (hσmin : 0 < σmin) (h211 : ∀ k, σmin ≤ σ k)
    (h26 : ∀ k, AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) < f (x k))
    (Lsub : ℕ → Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hsL : ∀ k, s k ∈ Lsub k)
    (hmin : ∀ k, ∀ t ∈ Lsub k,
      AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) ≤ AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) t)
    (ε : ℝ) (hε : 0 < ε) :
    let L₀ := max (σ 0) (3 / 2 * γ₂ * (C + L))
    let αcurv := σmin / (6 * L₀ ^ 3)
    ∀ k, ε < -lamMin (B k) (Lsub k) →
      αcurv * ε ^ 3 ≤ f (x k) - AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) := by sorry

end AdaptiveCubic.SecondOrder
