-- Prove2me | Theorems.Thm_AdaptiveCubic_FirstOrder_eq_5_23
-- name    : AdaptiveCubic.FirstOrder.eq_5_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:41:47.482151+00:00
-- url     : https://prove2.me/theorems/3450e754-3199-4382-8dab-fbe313bdf7d3
-- title:
--   Proof of Corollary 5.3, (5.23) — at most ⌈(2 + L̃ˢ₁)κᵘ_S⌉ unsuccessful iterations up to l₁
-- statement:
--   Consider a run of ARC(S) under the hypotheses of Corollary 5.3: AF.3, AF.4 (with $\kappa_H\ge1$ on an open convex set containing the iterates), AF.6 ($L>0$), AM.4 ($C>0$), (2.11) ($\sigma_k\ge\sigma_{\min}>0$), (2.6) for all $k$, and $f(x_k)\ge f_{\rm low}$ for all $k$. Let $\epsilon>0$ and assume $\|g_0\|>\epsilon$ and $\|g_1\|>\epsilon$. Let $l_1$ be the first index with $\|g_{l_1+1}\|\le\epsilon$ and $\mathcal U_{l_1}$ the unsuccessful iterations $k\le l_1$. Then
--
--   $$|\mathcal U_{l_1}|\le\left\lceil(2+\tilde L^s_1)\,\kappa^u_S\right\rceil,\qquad \kappa^u_S=\frac{\log(L_0/\sigma_{\min})}{\log\gamma_1},$$
--
--   where $\tilde L^s_1=\lceil\kappa^s_S\epsilon^{-3/2}\rceil$ (5.15) and $L_0=\max(\sigma_0,\tfrac32\gamma_2(C+L))$ (5.4).
--
--   Added to (5.22), this bounds the total number of iterations, and hence of function evaluations, before $\|g\|\le\epsilon$.
--
--   **Formalization Note** As in (5.22), the statement is quantified over every $j$ with $\|g_k\|>\epsilon$ for all $k\le j$ (exactly the $j\le l_1$). $|\mathcal U_j|$ is the number of $k\le j$ with $\rho_k<\eta_1$.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 15, proof of Corollary 5.3, (5.23); p. 14, (5.18)

import Mathlib
import Definitions.Def_AdaptiveCubic_FirstOrder_IsARCSRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.FirstOrder

/-- Proof of Corollary 5.3, (5.23), p. 15 (Cartis, Gould & Toint, ARC Part II, preprint rev.
15 Sep 2009).
Standing hypotheses: a run of ARC(S) (Algorithm 4.1, p. 12: Algorithm 2.1 with (4.1), (4.2),
TC.s (4.7) and (2.2)); AF.3 `f ∈ C²(ℝⁿ)` (5.1); AF.4 `‖g(y) − g(z)‖ ≤ κ_H‖y − z‖` on an open
convex `X` containing all iterates, `κ_H ≥ 1` (3.2); AF.6 `‖H(y) − H(z)‖ ≤ L‖y − z‖` for all
`y, z`, `L > 0` (5.2); AM.4 `‖(H(x_k) − B_k)s_k‖ ≤ C‖s_k‖²`, `C > 0` (5.3); (2.11)
`σ_k ≥ σ_min > 0`; and (2.6) `m_k(s_k) < f(x_k)` for all `k`, the standing assumption for ARC(S)
(p. 12, last paragraph of §4; p. 4). Here `g = ∇f`, `H = ∇²f = fderiv ℝ (gradient f)`.
Let `f(x_k) ≥ f_low` for all `k`, `ε > 0`, and assume (5.14) at `k = 0`
(`‖g₀‖ > ε` and `‖g₁‖ > ε`). Then `|U_{l₁}| ≤ ⌈(2 + L̃^s_1) κ^u_S⌉`, where `l₁` is the first
index with `‖g_{l₁+1}‖ ≤ ε`, `U_j` is the set of unsuccessful iterations `k ≤ j` (2.9),
`L̃^s_1 = ⌈κ^s_S ε^{−3/2}⌉` (5.15) and `κ^u_S = log(L₀/σ_min)/log γ₁` (5.18).
Formalized for every `j` with `‖g_k‖ > ε` for all `k ≤ j` (exactly the `j ≤ l₁`). -/
theorem eq_5_23 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ κθ : ℝ)
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
    (flow : ℝ) (hflow : ∀ k, flow ≤ f (x k))
    (ε : ℝ) (hε : 0 < ε)
    (h514 : ε < ‖gradient f (x 0)‖ ∧ ε < ‖gradient f (x 1)‖) :
    let L₀ := max (σ 0) (3 / 2 * γ₂ * (C + L))
    let κg := Real.sqrt ((1 - κθ) / (1 / 2 * L + C + L₀ + κθ * κH))
    let αS := σmin * κg ^ 3 / 6
    let κsS := (f (x 0) - flow) / (η₁ * αS)
    let κuS := Real.log (L₀ / σmin) / Real.log γ₁
    ∀ j, (∀ k ≤ j, ε < ‖gradient f (x k)‖) →
      (((Finset.range (j + 1)).filter
          (fun k => AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) < η₁)).card : ℤ) ≤
        ⌈(2 + (⌈κsS * ε ^ (-(3 / 2 : ℝ))⌉ : ℝ)) * κuS⌉ := by sorry

end AdaptiveCubic.FirstOrder
