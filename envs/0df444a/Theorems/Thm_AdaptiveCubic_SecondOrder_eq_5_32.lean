-- Prove2me | Theorems.Thm_AdaptiveCubic_SecondOrder_eq_5_32
-- name    : AdaptiveCubic.SecondOrder.eq_5_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:39:22.756116+00:00
-- url     : https://prove2.me/theorems/bfcd67e4-d4ca-442f-914a-39ebc082f463
-- title:
--   (5.32) — unsuccessful iterations up to l₂
-- statement:
--   Under the hypotheses of (5.30), let
--
--   $$\kappa^u_S=\frac{\log(L_0/\sigma_{\min})}{\log\gamma_1} \qquad (5.18)$$
--
--   and $L^s_2=\lceil\kappa_{\rm curv}\epsilon^{-3}\rceil$. For every $j$ such that $-\lambda_{\min}(Q_k^\top B_kQ_k)>\epsilon$ for all $k\le j$ (in particular for $j=l_2$, the last index before the curvature measure first drops to $\epsilon$),
--
--   $$|\mathcal U_j|\ \le\ \left\lceil (1+|\mathcal S_j|)\,\kappa^u_S\right\rceil\ \le\ \left\lceil (1+L^s_2)\,\kappa^u_S\right\rceil,$$
--
--   where $\mathcal S_j$ and $\mathcal U_j$ are the successful and unsuccessful iterations up to $j$ (2.9).
--
--   Together with $|\mathcal S_j|\le L^s_2$ this bounds the total number of iterations, hence function evaluations, before approximate nonnegative curvature in the subspace is reached.
--
--   **Formalization Note** Both inequalities of the chain are posed. "Up to $l_2$" is quantified as every $j$ with the negative-curvature condition at all $k\le j$, which never presumes that $l_2$ exists.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 16, proof of Corollary 5.4, (5.32); p. 14, (5.18)

import Mathlib
import Definitions.Def_AdaptiveCubic_SecondOrder_IsARCSRun
import Definitions.Def_AdaptiveCubic_SecondOrder_lamMin

open scoped RealInnerProductSpace

namespace AdaptiveCubic.SecondOrder

/-- Proof of Corollary 5.4, (5.32), p. 16 (Cartis, Gould & Toint, ARC Part II, preprint rev.
15 Sep 2009). For every `j` such that `−λ_min(Q_kᵀB_kQ_k) > ε` for all `k ≤ j` (in particular
`j = l₂`), `|U_j| ≤ ⌈(1 + |S_j|)κ^u_S⌉ ≤ ⌈(1 + L^s_2)κ^u_S⌉`, where `S_j`, `U_j` are the successful
and unsuccessful iterations `k ≤ j` (2.9), `L^s_2 = ⌈κ_curv ε^{−3}⌉` (5.25) and
`κ^u_S = log(L₀/σ_min)/log γ₁` (5.18).
Notation: `S` is the set of successful iterations (`ρ_k ≥ η₁`, (2.8)), `λ_k = λ_min(Q_kᵀB_kQ_k)` is
`lamMin (B k) (Lsub k)` for the subspace `L_k` = `Lsub k`, `L₀ = max(σ₀, (3/2)γ₂(C + L))` (5.4),
`α_curv = σ_min/(6L₀³)` and `κ_curv = (f(x₀) − f_low)/(η₁α_curv)` (5.26). Hypotheses: ARC(S) run
(Algorithm 4.1), AF.3, AF.6, AM.4 with `H = fderiv ℝ (gradient f)`, (2.11), (2.6) for all `k`
(p. 12, last paragraph of §4), `s_k` a global minimizer of `m_k` over `L_k`. Also `f(x_k) ≥ f_low` for all `k`. -/
theorem eq_5_32 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ κθ : ℝ)
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
    let κuS := Real.log (L₀ / σmin) / Real.log γ₁
    ∀ j : ℕ, (∀ k ≤ j, ε < -lamMin (B k) (Lsub k)) →
      (((Finset.range (j + 1)).filter
          (fun k => AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) < η₁)).card : ℤ) ≤
        ⌈(1 + (((Finset.range (j + 1)).filter
            (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℝ)) * κuS⌉ ∧
      ⌈(1 + (((Finset.range (j + 1)).filter
          (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℝ)) * κuS⌉ ≤
        ⌈(1 + (⌈κcurv * ε ^ (-3 : ℤ)⌉ : ℝ)) * κuS⌉ := by sorry

end AdaptiveCubic.SecondOrder
