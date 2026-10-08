-- Prove2me | Theorems.Thm_AdaptiveCubic_Cauchy_eq_3_22
-- name    : AdaptiveCubic.Cauchy.eq_3_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:23.124554+00:00
-- url     : https://prove2.me/theorems/80a546ed-8c71-47b0-8157-dfa8a775420e
-- title:
--   Corollary 3.4, proof, (3.22) — $|\mathcal U_j|\le\lceil-(\log\gamma_3/\log\gamma_1)L^s_1+\kappa^u_C/\epsilon\rceil$
-- statement:
--   Consider a run of the ARC algorithm with parameters $\gamma_2\ge\gamma_1>1$, $1>\eta_2\ge\eta_1>0$, $\sigma_0>0$, under AF.1, AF.4 (open convex set containing all iterates and trial points, $\kappa_H\ge1$) and AM.1 ($\kappa_B\ge0$), with $f(x_k)\ge f_{\rm low}$ for all $k$. Assume moreover that for some $\gamma_3\in(0,1]$, every very successful iteration $k$ has $\sigma_{k+1}\ge\gamma_3\sigma_k$ (2.10). Let $\epsilon\in(0,1]$. For every $j$ with $\|g_k\|>\epsilon$ for all $k=0,\dots,j$, the number of unsuccessful iterations among $0,\dots,j$ satisfies
--
--   $$
--   |\mathcal U_j|\le\left\lceil-\frac{\log\gamma_3}{\log\gamma_1}\,L^s_1+\frac{\kappa^u_C}{\epsilon}\right\rceil,\qquad \kappa^u_C=\frac{1}{\log\gamma_1}\max\left(1,\ \frac{\gamma_2\kappa_{HB}^2}{\sigma_0}\right),
--   $$
--
--   with $L^s_1=\lceil\kappa^s_C\epsilon^{-2}\rceil$ as in (3.15) and $\kappa^s_C$, $\alpha_C$, $\kappa_{HB}$ as in (3.16), (3.5).
--
--   Together with (3.21) this bounds the total number of iterations, hence of function evaluations, before $\|g\|\le\epsilon$.
--
--   **Formalization Note** Stated for every $j$ before which the gradient stays above $\epsilon$ (the paper's $j=j_1$). AF.4 is taken on a set containing the trial points, as in Lemma 3.2.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 9, proof of Corollary 3.4, (3.22) with (3.18)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- Proof of Corollary 3.4, (3.22), p. 9 (Cartis, Gould & Toint, ARC Part II, preprint rev.
15 Sep 2009). Under AF.1, AF.4, AM.1, `f(x_k) ≥ f_low` for all `k`, and (2.10) (`σ_{k+1} ≥ γ₃ σ_k` on
every very successful iteration, `γ₃ ∈ (0, 1]`), for `ϵ ∈ (0, 1]` and every `j` with `‖g_k‖ > ϵ` for
all `k = 0, …, j`: `|U_j| ≤ ⌈−(log γ₃/log γ₁) L^s_1 + κ^u_C/ϵ⌉`, with `L^s_1 = ⌈κ^s_C ϵ^{−2}⌉` (3.15),
`κ^u_C = (1/log γ₁) max(1, γ₂ κ_HB²/σ₀)` (3.18), and `κ^s_C`, `α_C`, `κ_HB` as in (3.16), (3.5).

Correction (AF.4): the page asks for an open convex set `X` containing all the iterates; the
proof of Lemma 3.2 applies AF.4 on the segment `[x_k, x_k + s_k]`, so `X` is also required to
contain every trial point `x_k + s_k` (on an unsuccessful iteration this is not an iterate). -/
theorem eq_3_22 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
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
    (γ₃ : ℝ) (hγ₃ : 0 < γ₃) (hγ₃' : γ₃ ≤ 1)
    (h210 : ∀ k, η₂ < rho f (B k) (σ k) (x k) (s k) → γ₃ * σ k ≤ σ (k + 1))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (j : ℕ) (hg : ∀ k ≤ j, ε < ‖gradient f (x k)‖) :
    let κHB := 108 * √2 / (1 - η₂) * (κH + κB)
    let αC := (6 * √2 * max (1 + κB) (2 * max (√(σ 0)) (κHB * √γ₂)))⁻¹
    let κsC := (f (x 0) - flow) / (η₁ * αC)
    let κuC := 1 / Real.log γ₁ * max 1 (γ₂ * κHB ^ 2 / σ 0)
    (((Finset.range (j + 1)).filter
        (fun k => rho f (B k) (σ k) (x k) (s k) < η₁)).card : ℤ) ≤
      ⌈-(Real.log γ₃ / Real.log γ₁) * (⌈κsC * ε ^ (-2 : ℤ)⌉ : ℝ) + κuC / ε⌉ := by sorry

end AdaptiveCubic.Cauchy
