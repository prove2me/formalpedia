-- Prove2me | Theorems.Thm_AdaptiveCubic_Cauchy_lemma_3_2
-- name    : AdaptiveCubic.Cauchy.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:41.259413+00:00
-- url     : https://prove2.me/theorems/fd04b37a-9128-46cc-bfb2-17e467510b06
-- title:
--   Lemma 3.2 — $\sqrt{\sigma_k\|g_k\|}>\kappa_{HB}$ forces a very successful iteration
-- statement:
--   Consider a run of the ARC algorithm with parameters $\gamma_2\ge\gamma_1>1$, $1>\eta_2\ge\eta_1>0$, $\sigma_0>0$, under the assumptions
--
--   1. AF.1: $f$ is continuously differentiable on $\mathbb R^n$;
--   2. AF.4: there is an open convex set $X$ containing every iterate $x_k$ and every trial point $x_k+s_k$, and $\kappa_H\ge1$, with $\|g(y)-g(z)\|\le\kappa_H\|y-z\|$ for all $y,z\in X$;
--   3. AM.1: $\|B_k\|\le\kappa_B$ for all $k$, with $\kappa_B\ge0$.
--
--   If at iteration $k$
--
--   $$
--   \sqrt{\sigma_k\|g_k\|}>\frac{108\sqrt2}{1-\eta_2}\,(\kappa_H+\kappa_B)=:\kappa_{HB}, \qquad (3.5)
--   $$
--
--   then iteration $k$ is very successful, $\rho_k>\eta_2$, and $\sigma_{k+1}\le\sigma_k$.
--
--   Large weights relative to the gradient force good agreement between model and function, so the weight cannot keep growing while the gradient is bounded away from zero.
--
--   **Formalization Note** The paper's AF.4 asks only that $X$ contain the iterates. Its proof applies the Lipschitz bound at a point of the segment $(x_k,x_k+s_k)$, which lies in $X$ only if the trial point does; on an unsuccessful iteration the trial point is not an iterate, and the printed lemma can fail when $f$ is irregular just outside a thin $X$. The set $X$ is therefore required to contain all trial points as well.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 7, Lemma 3.2, (3.1), (3.2), (3.5), (3.6)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- Lemma 3.2, p. 7 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009). Under AF.1
(`f ∈ C¹`), AF.4 (`∇f` is `κ_H`-Lipschitz on an open convex `X`, `κ_H ≥ 1`) and AM.1
(`‖B_k‖ ≤ κ_B`), if `√(σ_k ‖g_k‖) > κ_HB := 108√2 (κ_H + κ_B)/(1 − η₂)` (3.5), then iteration `k` is
very successful (`ρ_k > η₂`) and `σ_{k+1} ≤ σ_k` (3.6).

Correction (AF.4): the page asks for an open convex set `X` containing all the iterates; the
proof of Lemma 3.2 applies AF.4 on the segment `[x_k, x_k + s_k]`, so `X` is also required to
contain every trial point `x_k + s_k` (on an unsuccessful iteration this is not an iterate). -/
theorem lemma_3_2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (hf : ContDiff ℝ 1 f)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXo : IsOpen X) (hXc : Convex ℝ X)
    (hxX : ∀ k, x k ∈ X) (hxsX : ∀ k, x k + s k ∈ X)
    (κH : ℝ) (hκH : 1 ≤ κH)
    (hAF4 : ∀ y ∈ X, ∀ z ∈ X, ‖gradient f y - gradient f z‖ ≤ κH * ‖y - z‖)
    (κB : ℝ) (hκB : 0 ≤ κB) (hAM1 : ∀ k, ‖B k‖ ≤ κB)
    (k : ℕ)
    (h35 : 108 * √2 / (1 - η₂) * (κH + κB) < √(σ k * ‖gradient f (x k)‖)) :
    η₂ < rho f (B k) (σ k) (x k) (s k) ∧ σ (k + 1) ≤ σ k := by sorry

end AdaptiveCubic.Cauchy
