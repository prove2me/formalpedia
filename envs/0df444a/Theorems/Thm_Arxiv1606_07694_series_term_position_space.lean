-- Prove2me | Theorems.Thm_Arxiv1606_07694_series_term_position_space
-- name    : Arxiv1606_07694.series_term_position_space
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T23:33:42.234828+00:00
-- url     : https://prove2.me/theorems/1084389a-15c3-4c4d-93f6-660c67b5f02c
-- title:
--   Eq. (20): the terms of the perturbative series with second-order kernels, in position space
-- statement:
--   Let $h$ be a real Schwartz function on $\mathbb R^2$, fix $\mathbf k,\mathbf k_0$, and let $A\in\mathbb C$ and $D\in\mathbb C^{2\times2}$. Substitute the truncated kernel $A-D_{\mu\nu}\sum_{i<j}\mathbf k_i^\mu\mathbf k_j^\nu$ into the $n$-th term of the perturbative series (8). For $n=1$ the term equals $A\,\tilde h(\mathbf k-\mathbf k_0)$, and for every $n\ge2$ it equals
--   $$\int d^2\mathbf x\,e^{i(\mathbf k_0-\mathbf k)\cdot\mathbf x}\Big[\frac1{n!}A\,h^n(\mathbf x)+\frac{h^{n-2}(\mathbf x)}{2(n-2)!}D_{\mu\nu}\,\partial_\mu h(\mathbf x)\,\partial_\nu h(\mathbf x)\Big].\qquad(20)$$
--
--   This rewrites each order of the series in position space, where the sum over $n$ can be carried out.
--
--   **Formalization Note** The term of order $n=m+1$ is the Lean `seriesTerm` with index $m$. The $n=0$ term $(2\pi)^2\delta^{(2)}(\mathbf k_0-\mathbf k)R(\mathbf k_0)$ is a distribution and is not part of this statement. The Fourier normalization $\tilde h(\mathbf k)=\int h\,e^{-i\mathbf k\cdot\mathbf x}$ is the one under which (20) holds. The paper does not state it.
-- source:
--   G. Bimonte, Wave-scattering from a gently curved surface, arXiv:1606.07694v1 (2016), claim c010; Section "Resummation of the perturbative series", eq. (20), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1606_07694_Basic

open MeasureTheory Complex

namespace Arxiv1606_07694

theorem series_term_position_space (h : SchwartzMap Vec2 ℝ) (k k0 : Vec2) (a : ℂ)
    (Dm : Matrix (Fin 2) (Fin 2) ℂ) :
    seriesTerm h k k0 0 (truncPoly a Dm) = a * heightFT h (k - k0) ∧
    ∀ m : ℕ, seriesTerm h k k0 (m + 1) (truncPoly a Dm) =
      ∫ x : Vec2, Complex.exp (I * (inner ℝ (k0 - k) x : ℂ)) *
        (a * (h x : ℂ) ^ (m + 2) / ((m + 2).factorial : ℂ) +
          (h x : ℂ) ^ m / (2 * (m.factorial : ℂ)) *
            ∑ μ, ∑ ν, Dm μ ν * (heightPartial h μ x : ℂ) * (heightPartial h ν x : ℂ)) := by sorry

end Arxiv1606_07694
