-- Prove2me | Theorems.Thm_CompOT_NotHilbertian_prop_8_2_grid
-- name    : CompOT.NotHilbertian.prop_8_2_grid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:03.27268+00:00
-- url     : https://prove2.me/theorems/defb3353-a149-401d-a812-badb95572ad3
-- title:
--   Proof of Proposition 8.2 and Figure 8.6, pp. 507–508 — W_p² on the 1/4-grid measures over the four corners of the unit square is not negative definite (p = 1, 2)
-- statement:
--   Let $x^1=[0,0]$, $x^2=[1,0]$, $x^3=[0,1]$, $x^4=[1,1]$ be the corners of the unit square in $\mathbb R^2$, with the Euclidean distance. For a histogram $a$ on the grid of $\Sigma_4$ with increments $1/4$ (entries in $\{0,\frac14,\frac12,\frac34,1\}$ summing to $1$), let $\alpha_a=\sum_{k=1}^4a_k\delta_{x^k}$. Then for $p=1$ and for $p=2$ there are grid histograms $a^1,\dots,a^n$ and $r\in\mathbb R^n$ with $\sum_ir_i=0$ such that
--   $$\sum_{i,j=1}^n r_ir_j\,\mathcal W_p^2(\alpha_{a^i},\alpha_{a^j})>0.$$
--
--   The book establishes this numerically: the $35\times35$ matrix $\mathbf D_p$ of pairwise Wasserstein distances between the 35 grid measures has $J\mathbf D_p^2J$ with a positive eigenvalue (Figure 8.6). It is the explicit counterexample behind Proposition 8.2.
--
--   **Formalization Note** The conclusion is stated as the existence of a zero-sum vector with a positive quadratic form over grid measures (repetitions allowed), which is equivalent to the book's eigenvalue formulation for the 35 distinct grid measures (by the centering-matrix criterion). A proof needs exact values of the distances and an explicit certificate, not the floating-point computation of the figure.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 8.2, p. 507, and Figure 8.6, p. 508

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance
import Definitions.Def_CompOT_NotHilbertian_Defs

namespace CompOT.NotHilbertian

/-- Proof of Proposition 8.2, p. 507 (and Figure 8.6, p. 508): for `p = 1, 2` the squared
`p`-Wasserstein distances between the measures `∑ₖ aₖ δ_{xᵏ}` on the four corners
`x¹, …, x⁴` of the unit square, with `a` on the grid of `Σ₄` with increments `1/4`, are
not negative definite: some zero-sum `r` gives `∑_{i,j} rᵢ rⱼ W_p²(αᵢ, αⱼ) > 0`. -/
theorem prop_8_2_grid (p : ℝ) (hp : p = 1 ∨ p = 2) :
    ∃ (n : ℕ) (a : Fin n → Fin 4 → ℝ) (r : Fin n → ℝ),
      (∀ i, a i ∈ gridHists) ∧ ∑ i, r i = 0 ∧
        0 < ∑ i, ∑ j, r i * r j *
          wp p (discreteMeasure corners (a i)) (discreteMeasure corners (a j)) ^ 2 := by sorry

end CompOT.NotHilbertian
