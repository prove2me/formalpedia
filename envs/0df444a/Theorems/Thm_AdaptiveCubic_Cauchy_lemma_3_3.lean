-- Prove2me | Theorems.Thm_AdaptiveCubic_Cauchy_lemma_3_3
-- name    : AdaptiveCubic.Cauchy.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:20.583984+00:00
-- url     : https://prove2.me/theorems/c8ce4d24-8165-4dd4-b311-d02637449dbf
-- title:
--   Lemma 3.3 (3.13) — $\sigma_k\le\max(\sigma_0,\gamma_2\kappa_{HB}^2/\epsilon)$ while $\|g_k\|>\epsilon$
-- statement:
--   Consider a run of the ARC algorithm with parameters $\gamma_2\ge\gamma_1>1$, $1>\eta_2\ge\eta_1>0$, $\sigma_0>0$, under AF.1, AF.4 (on an open convex set containing all iterates and trial points, constant $\kappa_H\ge1$) and AM.1 (constant $\kappa_B\ge0$). Let $\epsilon>0$ and $j\ge0$ be such that $\|g_k\|>\epsilon$ for all $k=0,\dots,j$. Then
--
--   $$
--   \sigma_k\le\max\left(\sigma_0,\ \frac{\gamma_2}{\epsilon}\,\kappa_{HB}^2\right)\quad\text{for all }k=0,\dots,j,
--   $$
--
--   with $\kappa_{HB}=108\sqrt2\,(\kappa_H+\kappa_B)/(1-\eta_2)$ as in (3.5).
--
--   The weights stay bounded as long as the gradient stays large; this feeds both the model-decrease bound (3.20) and, through Theorem 2.1, the count of unsuccessful iterations.
--
--   **Formalization Note** The paper allows $j\le\infty$; the statement is given for every finite $j$, which covers the infinite case. AF.4 is taken on a set containing the trial points, as in Lemma 3.2.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 8, Lemma 3.3, (3.13)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- Lemma 3.3, (3.13), p. 8 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009). Under
AF.1, AF.4 and AM.1, let `ϵ > 0` with `‖g_k‖ > ϵ` for all `k = 0, …, j`. Then
`σ_k ≤ max(σ₀, (γ₂/ϵ) κ_HB²)` for all `k = 0, …, j`, where `κ_HB = 108√2 (κ_H + κ_B)/(1 − η₂)` (3.5).
The page's `j ≤ ∞` is covered by stating the result for every finite `j`.

Correction (AF.4): the page asks for an open convex set `X` containing all the iterates; the
proof of Lemma 3.2 applies AF.4 on the segment `[x_k, x_k + s_k]`, so `X` is also required to
contain every trial point `x_k + s_k` (on an unsuccessful iteration this is not an iterate). -/
theorem lemma_3_3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (hf : ContDiff ℝ 1 f)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXo : IsOpen X) (hXc : Convex ℝ X)
    (hxX : ∀ k, x k ∈ X) (hxsX : ∀ k, x k + s k ∈ X)
    (κH : ℝ) (hκH : 1 ≤ κH)
    (hAF4 : ∀ y ∈ X, ∀ z ∈ X, ‖gradient f y - gradient f z‖ ≤ κH * ‖y - z‖)
    (κB : ℝ) (hκB : 0 ≤ κB) (hAM1 : ∀ k, ‖B k‖ ≤ κB)
    (ε : ℝ) (hε : 0 < ε) (j : ℕ) (hg : ∀ k ≤ j, ε < ‖gradient f (x k)‖) :
    ∀ k ≤ j, σ k ≤ max (σ 0) (γ₂ / ε * (108 * √2 / (1 - η₂) * (κH + κB)) ^ 2) := by sorry

end AdaptiveCubic.Cauchy
