-- Prove2me | Theorems.Thm_AdaptiveCubic_FirstOrder_corollary_5_3
-- name    : AdaptiveCubic.FirstOrder.corollary_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:40:51.900024+00:00
-- url     : https://prove2.me/theorems/6f064a88-4bdf-4c88-8319-6f607f9e5740
-- title:
--   Corollary 5.3 — ARC(S) reaches ‖g‖ ≤ ε within ⌈κ_S ε^(−3/2)⌉ iterations
-- statement:
--   Let $f\in C^2(\mathbb R^n)$ (AF.3) with gradient $g$ and Hessian $H$, and consider a run of ARC(S) (Algorithm 4.1) with parameters $\gamma_2\ge\gamma_1>1$, $1>\eta_2\ge\eta_1>0$, $\sigma_0>0$ and TC.s constant $\kappa_\theta\in(0,1)$. Assume
--
--   1. AF.4: $\|g(x)-g(y)\|\le\kappa_H\|x-y\|$ on an open convex set containing all iterates, $\kappa_H\ge1$;
--   2. AF.6: $\|H(x)-H(y)\|\le L\|x-y\|$ for all $x,y$, $L>0$;
--   3. AM.4: $\|(H(x_k)-B_k)s_k\|\le C\|s_k\|^2$ for all $k$, $C>0$;
--   4. (2.11): $\sigma_k\ge\sigma_{\min}>0$ for all $k$;
--   5. (2.6): $m_k(s_k)<f(x_k)$ for all $k$;
--   6. $f(x_k)\ge f_{\rm low}$ for all $k$.
--
--   Let $\epsilon>0$, and define
--
--   $$L_0=\max\!\left(\sigma_0,\tfrac32\gamma_2(C+L)\right),\quad \kappa_g=\sqrt{\frac{1-\kappa_\theta}{\tfrac12L+C+L_0+\kappa_\theta\kappa_H}},\quad \alpha_S=\frac{\sigma_{\min}\kappa_g^3}{6},$$
--   $$\kappa^s_S=\frac{f(x_0)-f_{\rm low}}{\eta_1\alpha_S},\quad \kappa^u_S=\frac{\log(L_0/\sigma_{\min})}{\log\gamma_1},\quad \kappa_S=(1+\kappa^u_S)(2+\kappa^s_S).$$
--
--   Then:
--
--   1. the successful iterations with $\min(\|g_k\|,\|g_{k+1}\|)>\epsilon$ are finitely many, at most $\tilde L^s_1=\lceil\kappa^s_S\epsilon^{-3/2}\rceil$;
--   2. if $\|g_0\|>\epsilon$ and $\|g_1\|>\epsilon$, at most $\tilde L^s_1+1$ successful iterations occur up to the first index $l_1$ with $\|g_{l_1+1}\|\le\epsilon$;
--   3. if in addition $\epsilon\le1$, then
--
--   $$l_1\le\left\lceil\kappa_S\,\epsilon^{-3/2}\right\rceil.$$
--
--   So ARC(S) needs $O(\epsilon^{-3/2})$ iterations, function evaluations and gradient evaluations to reach $\|g\|\le\epsilon$, the order of Nesterov and Polyak's cubic-regularised Newton method, although the step is only an approximate model minimizer and $B_k$ only approximates the Hessian.
--
--   **Formalization Note** Parts 2 and 3 are quantified over every $j$ with $\|g_k\|>\epsilon$ for all $k\le j$, which are exactly the $j\le l_1$. Part 3 in this form also asserts that $l_1$ exists. Part 1 states that the set is finite and bounds its cardinality. (2.6) for all $k$ is the paper's standing assumption for ARC(S) (p. 12, last paragraph of §4; p. 4); it excludes runs that terminate. Powers of $\epsilon$ are real powers, ceilings are integer ceilings, and the constants are written out with `let` in the statement.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 14, Corollary 5.3, (5.14)–(5.18)

import Mathlib
import Definitions.Def_AdaptiveCubic_FirstOrder_IsARCSRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.FirstOrder

/-- Corollary 5.3, p. 14 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009).
Standing hypotheses: a run of ARC(S) (Algorithm 4.1, p. 12: Algorithm 2.1 with (4.1), (4.2),
TC.s (4.7) and (2.2)); AF.3 `f ∈ C²(ℝⁿ)` (5.1); AF.4 `‖g(y) − g(z)‖ ≤ κ_H‖y − z‖` on an open
convex `X` containing all iterates, `κ_H ≥ 1` (3.2); AF.6 `‖H(y) − H(z)‖ ≤ L‖y − z‖` for all
`y, z`, `L > 0` (5.2); AM.4 `‖(H(x_k) − B_k)s_k‖ ≤ C‖s_k‖²`, `C > 0` (5.3); (2.11)
`σ_k ≥ σ_min > 0`; and (2.6) `m_k(s_k) < f(x_k)` for all `k`, the standing assumption for ARC(S)
(p. 12, last paragraph of §4; p. 4). Here `g = ∇f`, `H = ∇²f = fderiv ℝ (gradient f)`.
Let `f(x_k) ≥ f_low` for all `k` and `ε > 0`. With `L₀ = max(σ₀, (3/2)γ₂(C + L))` (5.4),
`κ_g = √((1 − κ_θ)/(½L + C + L₀ + κ_θκ_H))` (5.6), `α_S = σ_min κ_g³/6`,
`κ^s_S = (f(x₀) − f_low)/(η₁ α_S)` (5.16), `κ^u_S = log(L₀/σ_min)/log γ₁`,
`κ_S = (1 + κ^u_S)(2 + κ^s_S)` (5.18):
1. the successful iterations with `min(‖g_k‖, ‖g_{k+1}‖) > ε` (5.14) are finitely many, at most
   `L̃^s_1 = ⌈κ^s_S ε^{−3/2}⌉` (5.15);
2. if (5.14) holds at `k = 0`, at most `L̃^s_1 + 1` successful iterations occur up to the first
   `l₁` with `‖g_{l₁+1}‖ ≤ ε`;
3. if moreover `ε ≤ 1`, then `l₁ ≤ ⌈κ_S ε^{−3/2}⌉` (5.17).
Parts 2 and 3 are stated for every `j` with `‖g_k‖ > ε` for all `k ≤ j` (exactly the
`j ≤ l₁`); part 3 in this form also asserts that `l₁` exists. -/
theorem corollary_5_3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ κθ : ℝ)
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
    (ε : ℝ) (hε : 0 < ε) :
    let L₀ := max (σ 0) (3 / 2 * γ₂ * (C + L))
    let κg := Real.sqrt ((1 - κθ) / (1 / 2 * L + C + L₀ + κθ * κH))
    let αS := σmin * κg ^ 3 / 6
    let κsS := (f (x 0) - flow) / (η₁ * αS)
    let κuS := Real.log (L₀ / σmin) / Real.log γ₁
    let κS := (1 + κuS) * (2 + κsS)
    ({k | η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧
        ε < min ‖gradient f (x k)‖ ‖gradient f (x (k + 1))‖}.Finite ∧
      ({k | η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) ∧
        ε < min ‖gradient f (x k)‖ ‖gradient f (x (k + 1))‖}.ncard : ℤ) ≤
        ⌈κsS * ε ^ (-(3 / 2 : ℝ))⌉) ∧
    (ε < ‖gradient f (x 0)‖ ∧ ε < ‖gradient f (x 1)‖ →
      ∀ j, (∀ k ≤ j, ε < ‖gradient f (x k)‖) →
        (((Finset.range (j + 1)).filter
            (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℤ) ≤
          ⌈κsS * ε ^ (-(3 / 2 : ℝ))⌉ + 1) ∧
    (ε < ‖gradient f (x 0)‖ ∧ ε < ‖gradient f (x 1)‖ → ε ≤ 1 →
      ∀ j, (∀ k ≤ j, ε < ‖gradient f (x k)‖) →
        (j : ℤ) ≤ ⌈κS * ε ^ (-(3 / 2 : ℝ))⌉) := by sorry

end AdaptiveCubic.FirstOrder
