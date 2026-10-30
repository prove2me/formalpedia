-- Prove2me | Theorems.Thm_FiniteEnergyPlane_norm_iteratedFDeriv_succ_le_of_halfPlane
-- name    : FiniteEnergyPlane.norm_iteratedFDeriv_succ_le_of_halfPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-29T20:48:03.280355+00:00
-- url     : https://prove2.me/theorems/785b282d-f97b-452c-9c6e-ede164eda6ec
-- title:
--   Bound on an intermediate derivative of a smooth map on a half-plane by its neighbouring derivatives
-- statement:
--   Let $F$ be a real normed space, $s_0\in\mathbb{R}$, and let $f:\mathbb{R}\times\mathbb{R}\to F$ be $C^\infty$ on the open half-plane $(s_0,\infty)\times\mathbb{R}$. Let $j\in\mathbb{N}$, let $p=(p_1,p_2)$ with $p_1>s_0$, and let $A,B\in\mathbb{R}$, $h>0$. Suppose that for every $q$ with $q_1\ge p_1$ we have $\|D^jf(q)\|\le A$ and $\|D^{j+2}f(q)\|\le B$. Then
--   $$\|D^{j+1}f(p)\|\le 2\Big(\frac{2A}{h}+Bh\Big).$$
--
--   This is a pointwise interpolation inequality for consecutive derivative orders on a half-plane, using only the region to the right of the point. It is meant for estimating derivatives of maps defined on cylindrical ends.
--
--   **Formalization Note** $D^kf$ is `iteratedFDeriv ℝ k f`, with the norm of continuous multilinear maps on `ℝ × ℝ` (sup norm). The half-plane is `Set.Ioi s₀ ×ˢ Set.univ`, and the bounds are assumed on `{q | p.1 ≤ q.1}`.
-- source:
--   Elementary real analysis (Landau-Kolmogorov type inequality); used for U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 2.10

import Mathlib

namespace FiniteEnergyPlane

open scoped ContDiff

/-- On a half-plane `{s > s₀}`, the norm of the `(j+1)`-st derivative of a smooth map at `p` is
bounded by `2 (2A/h + Bh)` for every `h > 0`, where `A` and `B` bound the `j`-th and `(j+2)`-nd
derivatives on `{s ≥ p.1}`. -/
theorem norm_iteratedFDeriv_succ_le_of_halfPlane {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : ℝ × ℝ → F) (s₀ : ℝ)
    (hf : ContDiffOn ℝ ∞ f (Set.Ioi s₀ ×ˢ Set.univ)) (j : ℕ) (p : ℝ × ℝ) (hp : s₀ < p.1)
    (A B h : ℝ) (hh : 0 < h)
    (hA : ∀ q : ℝ × ℝ, p.1 ≤ q.1 → ‖iteratedFDeriv ℝ j f q‖ ≤ A)
    (hB : ∀ q : ℝ × ℝ, p.1 ≤ q.1 → ‖iteratedFDeriv ℝ (j + 2) f q‖ ≤ B) :
    ‖iteratedFDeriv ℝ (j + 1) f p‖ ≤ 2 * (2 * A / h + B * h) := by
  sorry

end FiniteEnergyPlane
