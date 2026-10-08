-- Prove2me | Theorems.Thm_AdaptiveCubic_Cauchy_corollary_3_4
-- name    : AdaptiveCubic.Cauchy.corollary_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:00.914492+00:00
-- url     : https://prove2.me/theorems/3e9bad40-8a61-4f41-99f9-3e921fc15f47
-- title:
--   Corollary 3.4 — basic ARC reaches $\|g\|\le\epsilon$ within $\lceil\kappa^s_C\epsilon^{-2}\rceil$ successful and $\lceil\kappa_C\epsilon^{-2}\rceil$ total iterations
-- statement:
--   Consider a run of the ARC algorithm (Algorithm 2.1, steps satisfying the Cauchy condition) with parameters $\gamma_2\ge\gamma_1>1$, $1>\eta_2\ge\eta_1>0$, $\sigma_0>0$, under
--
--   1. AF.1: $f\in C^1(\mathbb R^n)$;
--   2. AF.4: $\|g(y)-g(z)\|\le\kappa_H\|y-z\|$ for all $y,z$ in an open convex set $X$ containing every iterate $x_k$ and every trial point $x_k+s_k$, with $\kappa_H\ge1$;
--   3. AM.1: $\|B_k\|\le\kappa_B$ for all $k$, with $\kappa_B\ge0$;
--
--   and suppose $f(x_k)\ge f_{\rm low}$ for all $k$. Let $\epsilon\in(0,1]$ with $\|g_0\|>\epsilon$, and let $j_1\le\infty$ be the first iteration with $\|g_{j_1+1}\|\le\epsilon$. Define
--
--   $$
--   \kappa_{HB}=\frac{108\sqrt2}{1-\eta_2}(\kappa_H+\kappa_B),\quad
--   \alpha_C=\Big[6\sqrt2\max\big(1+\kappa_B,\ 2\max(\sqrt{\sigma_0},\kappa_{HB}\sqrt{\gamma_2})\big)\Big]^{-1},\quad
--   \kappa^s_C=\frac{f(x_0)-f_{\rm low}}{\eta_1\alpha_C}.
--   $$
--
--   1. The number of successful iterations up to $j_1$ is at most
--   $$L^s_1=\left\lceil\kappa^s_C\,\epsilon^{-2}\right\rceil .$$
--   2. If moreover $\sigma_{k+1}\ge\gamma_3\sigma_k$ on every very successful iteration $k$, for some $\gamma_3\in(0,1]$ (2.10), then
--   $$
--   j_1\le L_1=\left\lceil\kappa_C\,\epsilon^{-2}\right\rceil,\qquad
--   \kappa_C=\left(1-\frac{\log\gamma_3}{\log\gamma_1}\right)\kappa^s_C+\kappa^u_C,\quad
--   \kappa^u_C=\frac{1}{\log\gamma_1}\max\left(1,\frac{\gamma_2\kappa_{HB}^2}{\sigma_0}\right).
--   $$
--   In particular $j_1$ is finite.
--
--   So ARC with only the Cauchy condition on the step needs $O(\epsilon^{-2})$ gradient evaluations and $O(\epsilon^{-2})$ function evaluations to reach an approximately first-order critical point, the same order as steepest descent.
--
--   **Formalization Note** Both conclusions are stated for every $j$ such that $\|g_k\|>\epsilon$ for all $k=0,\dots,j$: such $j$ are exactly the indices up to $j_1$, so bounding all of them (including the count of successful iterations among $0,\dots,j$) is equivalent to the printed bound on $j_1$ and also asserts that $j_1$ is finite, without presupposing it. Condition (2.10), with its $\gamma_3$, is a hypothesis of the second conclusion only. The constants are written out as in (3.5), (3.15)–(3.18). The paper's AF.4 asks only that $X$ contain the iterates; Lemma 3.2's proof also needs the trial points in $X$, so that is assumed (see Lemma 3.2). The second bound is true as printed, although it follows from the unrounded forms of (3.15) and (3.22) rather than by adding the two ceilings as the paper's last line suggests.
-- source:
--   Cartis, Gould & Toint, Adaptive cubic regularisation methods for unconstrained optimization. Part II, preprint rev. 15 Sep 2009 (UNamur), p. 9, Corollary 3.4, (3.15)–(3.18)

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

namespace AdaptiveCubic.Cauchy

/-- Corollary 3.4, p. 9 (Cartis, Gould & Toint, ARC Part II, preprint rev. 15 Sep 2009). Let AF.1,
AF.4 and AM.1 hold and `f(x_k) ≥ f_low` for all `k`. Let `ϵ ∈ (0, 1]` with `‖g_0‖ > ϵ`.
1. (3.15) Every `j` with `‖g_k‖ > ϵ` for all `k = 0, …, j` has at most `L^s_1 = ⌈κ^s_C ϵ^{−2}⌉`
   successful iterations `k ≤ j`, where `κ^s_C = (f(x_0) − f_low)/(η₁ α_C)`,
   `α_C = [6√2 max(1 + κ_B, 2 max(√σ₀, κ_HB √γ₂))]⁻¹` (3.16), `κ_HB = 108√2 (κ_H + κ_B)/(1 − η₂)` (3.5).
2. (3.17) If moreover (2.10) holds (`σ_{k+1} ≥ γ₃ σ_k` on every very successful iteration,
   `γ₃ ∈ (0, 1]`), every such `j` satisfies `j ≤ L_1 = ⌈κ_C ϵ^{−2}⌉`, where
   `κ_C = (1 − log γ₃/log γ₁) κ^s_C + κ^u_C` and `κ^u_C = (1/log γ₁) max(1, γ₂ κ_HB²/σ₀)` (3.18).
The page's `j₁ ≤ ∞`, the first iteration with `‖g_{j₁+1}‖ ≤ ϵ`, is the largest such `j`; bounding
every such `j` says that `j₁` is finite and obeys the bound.

Correction (AF.4): the page asks for an open convex set `X` containing all the iterates; the
proof of Lemma 3.2 applies AF.4 on the segment `[x_k, x_k + s_k]`, so `X` is also required to
contain every trial point `x_k + s_k` (on an unsuccessful iteration this is not an iterate). -/
theorem corollary_3_4 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
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
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hg0 : ε < ‖gradient f (x 0)‖) :
    let κHB := 108 * √2 / (1 - η₂) * (κH + κB)
    let αC := (6 * √2 * max (1 + κB) (2 * max (√(σ 0)) (κHB * √γ₂)))⁻¹
    let κsC := (f (x 0) - flow) / (η₁ * αC)
    (∀ j : ℕ, (∀ k ≤ j, ε < ‖gradient f (x k)‖) →
      (((Finset.range (j + 1)).filter
          (fun k => η₁ ≤ rho f (B k) (σ k) (x k) (s k))).card : ℤ) ≤ ⌈κsC * ε ^ (-2 : ℤ)⌉) ∧
    ∀ γ₃ : ℝ, 0 < γ₃ → γ₃ ≤ 1 →
      (∀ k, η₂ < rho f (B k) (σ k) (x k) (s k) → γ₃ * σ k ≤ σ (k + 1)) →
      let κuC := 1 / Real.log γ₁ * max 1 (γ₂ * κHB ^ 2 / σ 0)
      let κC := (1 - Real.log γ₃ / Real.log γ₁) * κsC + κuC
      ∀ j : ℕ, (∀ k ≤ j, ε < ‖gradient f (x k)‖) → (j : ℤ) ≤ ⌈κC * ε ^ (-2 : ℤ)⌉ := by sorry

end AdaptiveCubic.Cauchy
