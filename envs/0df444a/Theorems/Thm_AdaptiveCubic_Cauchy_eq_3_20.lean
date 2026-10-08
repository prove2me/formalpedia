-- Prove2me | Theorems.Thm_AdaptiveCubic_Cauchy_eq_3_20
-- name    : AdaptiveCubic.Cauchy.eq_3_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:53.967872+00:00
-- url     : https://prove2.me/theorems/b4339739-d1e0-4665-b9c7-45c7bccf65b0
-- title:
--   Corollary 3.4, proof, (3.20) — model decrease $f(x_k)-m_k(s_k)\ge\alpha_C\epsilon^2$
-- statement:
--   Consider a run of the ARC algorithm with parameters $\gamma_2\ge\gamma_1>1$, $1>\eta_2\ge\eta_1>0$, $\sigma_0>0$, under AF.1, AF.4 (open convex set containing all iterates and trial points, $\kappa_H\ge1$) and AM.1 ($\kappa_B\ge0$). Let $\epsilon\in(0,1]$ and $j\ge0$ with $\|g_k\|>\epsilon$ for all $k=0,\dots,j$. Then
--
--   $$
--   f(x_k)-m_k(s_k)\ge\alpha_C\,\epsilon^2\quad\text{for all }k=0,\dots,j,
--   $$
--
--   where
--
--   $$
--   \alpha_C=\Big[6\sqrt2\,\max\big(1+\kappa_B,\ 2\max(\sqrt{\sigma_0},\ \kappa_{HB}\sqrt{\gamma_2})\big)\Big]^{-1},\qquad \kappa_{HB}=\frac{108\sqrt2}{1-\eta_2}(\kappa_H+\kappa_B).
--   $$
--
--   This is the hypothesis (2.18) of Theorem 2.2 with $p=2$, which turns into the $\epsilon^{-2}$ bound on successful iterations.
--
--   **Formalization Note** In the paper this display is part of the proof of Corollary 3.4, with $j=j_1$; here it is stated for every $j$ before which the gradient stays above $\epsilon$. The lower bound $f_{\rm low}$ of the corollary is not needed and is omitted.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 9, proof of Corollary 3.4, (3.20) with (3.16)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- Proof of Corollary 3.4, (3.20), p. 9 (Cartis, Gould & Toint, ARC Part II, preprint rev.
15 Sep 2009). Under AF.1, AF.4 and AM.1, for `ϵ ∈ (0, 1]` and `j` with `‖g_k‖ > ϵ` for all
`k = 0, …, j`: `f(x_k) − m_k(s_k) ≥ α_C ϵ²` for all `k = 0, …, j`, where
`α_C = [6√2 max(1 + κ_B, 2 max(√σ₀, κ_HB √γ₂))]⁻¹` (3.16) and `κ_HB = 108√2 (κ_H + κ_B)/(1 − η₂)` (3.5).

Correction (AF.4): the page asks for an open convex set `X` containing all the iterates; the
proof of Lemma 3.2 applies AF.4 on the segment `[x_k, x_k + s_k]`, so `X` is also required to
contain every trial point `x_k + s_k` (on an unsuccessful iteration this is not an iterate). -/
theorem eq_3_20 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (hf : ContDiff ℝ 1 f)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXo : IsOpen X) (hXc : Convex ℝ X)
    (hxX : ∀ k, x k ∈ X) (hxsX : ∀ k, x k + s k ∈ X)
    (κH : ℝ) (hκH : 1 ≤ κH)
    (hAF4 : ∀ y ∈ X, ∀ z ∈ X, ‖gradient f y - gradient f z‖ ≤ κH * ‖y - z‖)
    (κB : ℝ) (hκB : 0 ≤ κB) (hAM1 : ∀ k, ‖B k‖ ≤ κB)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (j : ℕ) (hg : ∀ k ≤ j, ε < ‖gradient f (x k)‖) :
    let κHB := 108 * √2 / (1 - η₂) * (κH + κB)
    let αC := (6 * √2 * max (1 + κB) (2 * max (√(σ 0)) (κHB * √γ₂)))⁻¹
    ∀ k ≤ j, αC * ε ^ 2 ≤ f (x k) - model f (B k) (σ k) (x k) (s k) := by sorry

end AdaptiveCubic.Cauchy
