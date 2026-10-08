-- Prove2me | Theorems.Thm_AdaptiveCubic_FirstOrder_lemma_5_2
-- name    : AdaptiveCubic.FirstOrder.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:40:49.135464+00:00
-- url     : https://prove2.me/theorems/9db8b6e6-b3ac-4251-9d39-4a36ae5c2245
-- title:
--   Lemma 5.2 — under TC.s, ‖s_k‖ ≥ κ_g √‖g_{k+1}‖ on successful iterations
-- statement:
--   Let $f\in C^2(\mathbb R^n)$ (AF.3) with gradient $g$ and Hessian $H$, and consider a run of ARC (Algorithm 2.1) whose steps satisfy the termination criterion TC.s (4.7) with constant $\kappa_\theta\in(0,1)$. Assume
--
--   1. AF.4: $\|g(x)-g(y)\|\le\kappa_H\|x-y\|$ for all $x,y$ in an open convex set $X$ containing every iterate $x_k$, with $\kappa_H\ge1$;
--   2. AF.6: $\|H(x)-H(y)\|\le L\|x-y\|$ for all $x,y\in\mathbb R^n$, with $L>0$;
--   3. AM.4: $\|(H(x_k)-B_k)s_k\|\le C\|s_k\|^2$ for all $k$, with $C>0$;
--   4. (2.6): $m_k(s_k)<f(x_k)$ for all $k$.
--
--   Then for every successful iteration $k$ (that is, $\rho_k\ge\eta_1$)
--
--   $$\|s_k\|\ge\kappa_g\sqrt{\|g_{k+1}\|},\qquad \kappa_g=\sqrt{\frac{1-\kappa_\theta}{\tfrac12L+C+L_0+\kappa_\theta\kappa_H}},$$
--
--   with $L_0=\max(\sigma_0,\tfrac32\gamma_2(C+L))$ from Lemma 5.1.
--
--   An accepted step cannot be short unless the gradient at the new iterate is small. Together with Lemma 4.2 this is what improves the model decrease from order $\epsilon^2$ to order $\epsilon^{3/2}$.
--
--   **Formalization Note** The page's hypothesis list is AF.3–AF.4, AF.6, AM.4 and TC.s; the proof invokes Lemma 5.1, which holds "as long as (2.6) holds" (p. 13), so (2.6) for all $k$ is an explicit hypothesis. Conditions (4.1)–(4.2) are not assumed: the run is an ARC run plus TC.s.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 13, Lemma 5.2, (5.5)–(5.6); p. 7, AF.4 (3.2)

import Mathlib
import Definitions.Def_AdaptiveCubic_FirstOrder_IsARCSRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.FirstOrder

/-- Lemma 5.2, p. 13 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009).
Let AF.3 (`f ∈ C²(ℝⁿ)`, (5.1)), AF.4 (`‖g(y) − g(z)‖ ≤ κ_H‖y − z‖` for `y, z` in an open convex set
`X` containing all iterates, `κ_H ≥ 1`, (3.2)), AF.6 (`‖H(y) − H(z)‖ ≤ L‖y − z‖` for all `y, z`,
`L > 0`, (5.2)), AM.4 (`‖(H(x_k) − B_k)s_k‖ ≤ C‖s_k‖²` for all `k`, `C > 0`, (5.3)) and TC.s (4.7)
hold, where `g = ∇f` and `H = ∇²f` is `fderiv ℝ (gradient f)`. Then for every successful iteration
`k` (`ρ_k ≥ η₁`), `‖s_k‖ ≥ κ_g √‖g_{k+1}‖` (5.5), where
`κ_g = √((1 − κ_θ)/(½L + C + L₀ + κ_θ κ_H))` (5.6) and `L₀ = max(σ₀, (3/2)γ₂(C + L))` (5.4).
The proof uses Lemma 5.1, which the page applies "as long as (2.6) holds" (p. 13); (2.6),
`m_k(s_k) < f(x_k)` for all `k` (standing assumption for ARC(S), p. 12), is a hypothesis. -/
theorem lemma_5_2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ κθ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : AdaptiveCubic.Cauchy.IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (hTCs : TCs f κθ x s σ B)
    (hAF3 : ContDiff ℝ 2 f)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXo : IsOpen X) (hXc : Convex ℝ X)
    (hxX : ∀ k, x k ∈ X) (κH : ℝ) (hκH : 1 ≤ κH)
    (hAF4 : ∀ y ∈ X, ∀ z ∈ X, ‖gradient f y - gradient f z‖ ≤ κH * ‖y - z‖)
    (L : ℝ) (hL : 0 < L)
    (hAF6 : ∀ y z, ‖fderiv ℝ (gradient f) y - fderiv ℝ (gradient f) z‖ ≤ L * ‖y - z‖)
    (C : ℝ) (hC : 0 < C)
    (hAM4 : ∀ k, ‖(fderiv ℝ (gradient f) (x k) - B k) (s k)‖ ≤ C * ‖s k‖ ^ 2)
    (h26 : ∀ k, AdaptiveCubic.Cauchy.model f (B k) (σ k) (x k) (s k) < f (x k)) :
    ∀ k, η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) →
      Real.sqrt ((1 - κθ) /
          (1 / 2 * L + C + max (σ 0) (3 / 2 * γ₂ * (C + L)) + κθ * κH)) *
        Real.sqrt ‖gradient f (x (k + 1))‖ ≤ ‖s k‖ := by sorry

end AdaptiveCubic.FirstOrder
