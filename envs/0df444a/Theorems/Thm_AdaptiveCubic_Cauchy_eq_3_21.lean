-- Prove2me | Theorems.Thm_AdaptiveCubic_Cauchy_eq_3_21
-- name    : AdaptiveCubic.Cauchy.eq_3_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:41.226793+00:00
-- url     : https://prove2.me/theorems/6438c519-84e3-46d0-bfbf-75986e5fc7fb
-- title:
--   Corollary 3.4, proof, (3.21) — $|\mathcal S_j|\le\lceil\kappa^s_C\epsilon^{-2}\rceil$ while $\|g_k\|>\epsilon$
-- statement:
--   Consider a run of the ARC algorithm with parameters $\gamma_2\ge\gamma_1>1$, $1>\eta_2\ge\eta_1>0$, $\sigma_0>0$, under AF.1, AF.4 (open convex set containing all iterates and trial points, $\kappa_H\ge1$) and AM.1 ($\kappa_B\ge0$), and let $f(x_k)\ge f_{\rm low}$ for all $k$. Let $\epsilon\in(0,1]$. For every $j$ with $\|g_k\|>\epsilon$ for all $k=0,\dots,j$, the number of successful iterations among $0,\dots,j$ satisfies
--
--   $$
--   |\mathcal S_j|\le L^s_1=\left\lceil\kappa^s_C\,\epsilon^{-2}\right\rceil,\qquad \kappa^s_C=\frac{f(x_0)-f_{\rm low}}{\eta_1\alpha_C},
--   $$
--
--   with $\alpha_C$ and $\kappa_{HB}$ as in (3.16) and (3.5).
--
--   This is the first part of Corollary 3.4: the number of gradient evaluations before $\|g\|\le\epsilon$ is $O(\epsilon^{-2})$.
--
--   **Formalization Note** The paper states this for $j=j_1$, the last index with $\|g_k\|>\epsilon$; bounding every such $j$ is equivalent and also covers the case where the gradient never drops below $\epsilon$. AF.4 is taken on a set containing the trial points, as in Lemma 3.2.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 9, proof of Corollary 3.4, (3.21) with (3.15), (3.16)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- Proof of Corollary 3.4, (3.21), p. 9 (Cartis, Gould & Toint, ARC Part II, preprint rev.
15 Sep 2009): the first part of Corollary 3.4. Under AF.1, AF.4, AM.1 and `f(x_k) ≥ f_low` for all
`k`, for `ϵ ∈ (0, 1]` and every `j` with `‖g_k‖ > ϵ` for all `k = 0, …, j`, the number of successful
iterations `k ≤ j` satisfies `|S_j| ≤ L^s_1 = ⌈κ^s_C ϵ^{−2}⌉` (3.15), with
`κ^s_C = (f(x_0) − f_low)/(η₁ α_C)` and `α_C`, `κ_HB` as in (3.16), (3.5).

Correction (AF.4): the page asks for an open convex set `X` containing all the iterates; the
proof of Lemma 3.2 applies AF.4 on the segment `[x_k, x_k + s_k]`, so `X` is also required to
contain every trial point `x_k + s_k` (on an unsuccessful iteration this is not an iterate). -/
theorem eq_3_21 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (hf : ContDiff ℝ 1 f)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hXo : IsOpen X) (hXc : Convex ℝ X)
    (hxX : ∀ k, x k ∈ X) (hxsX : ∀ k, x k + s k ∈ X)
    (κH : ℝ) (hκH : 1 ≤ κH)
    (hAF4 : ∀ y ∈ X, ∀ z ∈ X, ‖gradient f y - gradient f z‖ ≤ κH * ‖y - z‖)
    (κB : ℝ) (hκB : 0 ≤ κB) (hAM1 : ∀ k, ‖B k‖ ≤ κB)
    (flow : ℝ) (hlow : ∀ k, flow ≤ f (x k))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (j : ℕ) (hg : ∀ k ≤ j, ε < ‖gradient f (x k)‖) :
    let κHB := 108 * √2 / (1 - η₂) * (κH + κB)
    let αC := (6 * √2 * max (1 + κB) (2 * max (√(σ 0)) (κHB * √γ₂)))⁻¹
    let κsC := (f (x 0) - flow) / (η₁ * αC)
    (((Finset.range (j + 1)).filter
          (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k))).card : ℤ) ≤ ⌈κsC * ε ^ (-2 : ℤ)⌉ := by sorry

end AdaptiveCubic.Cauchy
