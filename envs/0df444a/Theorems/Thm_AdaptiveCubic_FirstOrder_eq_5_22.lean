-- Prove2me | Theorems.Thm_AdaptiveCubic_FirstOrder_eq_5_22
-- name    : AdaptiveCubic.FirstOrder.eq_5_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:40:52.317546+00:00
-- url     : https://prove2.me/theorems/b85794b3-b324-441c-bb67-61b97d82db0b
-- title:
--   Proof of Corollary 5.3, (5.22) — at most L̃ˢ₁ + 1 successful iterations up to l₁
-- statement:
--   Consider a run of ARC(S) under the hypotheses of Corollary 5.3: AF.3, AF.4 (with $\kappa_H\ge1$ on an open convex set containing the iterates), AF.6 ($L>0$), AM.4 ($C>0$), (2.11) ($\sigma_k\ge\sigma_{\min}>0$), (2.6) for all $k$, and $f(x_k)\ge f_{\rm low}$ for all $k$. Let $\epsilon>0$ and assume (5.14) at $k=0$, i.e. $\|g_0\|>\epsilon$ and $\|g_1\|>\epsilon$. Let $l_1$ be the first index with $\|g_{l_1+1}\|\le\epsilon$ and $\mathcal S_{l_1}$ the successful iterations $k\le l_1$. Then
--
--   $$|\mathcal S_{l_1}|\le\tilde L^s_1+1,\qquad \tilde L^s_1=\left\lceil\kappa^s_S\,\epsilon^{-3/2}\right\rceil,\quad \kappa^s_S=\frac{f(x_0)-f_{\rm low}}{\eta_1\alpha_S},$$
--
--   with $\alpha_S=\sigma_{\min}\kappa_g^3/6$, $\kappa_g$ from (5.6) and $L_0$ from (5.4).
--
--   This is the count of gradient evaluations needed to reach $\|g\|\le\epsilon$, the second assertion of Corollary 5.3.
--
--   **Formalization Note** The statement is quantified over every $j$ such that $\|g_k\|>\epsilon$ for all $k\le j$; these are exactly the $j\le l_1$, so the bound for all of them is the bound at $l_1$, and it does not presuppose that $l_1$ exists. $|\mathcal S_j|$ is the number of $k\le j$ with $\rho_k\ge\eta_1$.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 15, proof of Corollary 5.3, (5.22); p. 14, (5.15)–(5.16)

import Mathlib
import Definitions.Def_AdaptiveCubic_FirstOrder_IsARCSRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.FirstOrder

/-- Proof of Corollary 5.3, (5.22), p. 15 (Cartis, Gould & Toint, ARC Part II, preprint rev.
15 Sep 2009).
Standing hypotheses: a run of ARC(S) (Algorithm 4.1, p. 12: Algorithm 2.1 with (4.1), (4.2),
TC.s (4.7) and (2.2)); AF.3 `f ∈ C²(ℝⁿ)` (5.1); AF.4 `‖g(y) − g(z)‖ ≤ κ_H‖y − z‖` on an open
convex `X` containing all iterates, `κ_H ≥ 1` (3.2); AF.6 `‖H(y) − H(z)‖ ≤ L‖y − z‖` for all
`y, z`, `L > 0` (5.2); AM.4 `‖(H(x_k) − B_k)s_k‖ ≤ C‖s_k‖²`, `C > 0` (5.3); (2.11)
`σ_k ≥ σ_min > 0`; and (2.6) `m_k(s_k) < f(x_k)` for all `k`, the standing assumption for ARC(S)
(p. 12, last paragraph of §4; p. 4). Here `g = ∇f`, `H = ∇²f = fderiv ℝ (gradient f)`.
Let `f(x_k) ≥ f_low` for all `k`, `ε > 0`, and assume (5.14) at `k = 0`
(`‖g₀‖ > ε` and `‖g₁‖ > ε`). Then `|S_{l₁}| ≤ L̃^s_1 + 1`, where `l₁` is the first index with
`‖g_{l₁+1}‖ ≤ ε`, `S_j` is the set of successful iterations `k ≤ j` (2.9) and
`L̃^s_1 = ⌈κ^s_S ε^{−3/2}⌉` (5.15), `κ^s_S = (f(x₀) − f_low)/(η₁ α_S)` (5.16).
Formalized for every `j` with `‖g_k‖ > ε` for all `k ≤ j` (exactly the `j ≤ l₁`). -/
theorem eq_5_22 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ κθ : ℝ)
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
          (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℤ) ≤
        ⌈κsS * ε ^ (-(3 / 2 : ℝ))⌉ + 1 := by sorry

end AdaptiveCubic.FirstOrder
