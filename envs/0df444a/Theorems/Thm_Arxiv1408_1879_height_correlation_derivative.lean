-- Prove2me | Theorems.Thm_Arxiv1408_1879_height_correlation_derivative
-- name    : Arxiv1408_1879.height_correlation_derivative
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T12:24:16.860176+00:00
-- url     : https://prove2.me/theorems/2b1435c0-5d41-4e9a-b0f9-d30c1ad753d9
-- title:
--   Eq. (36): explicit evaluation of the derivative in eq. (28)
-- statement:
--   Let $k>0$, $\theta,X\in\mathbb{R}$, $r>0$, $S=\sin\theta-1$, and let $\rho:\mathbb{R}\to\mathbb{R}$ be continuously differentiable. Then
--   $$ik\cos\theta\,\frac{d}{dr}\left[\int_0^r\frac{e^{ikSr'}}{\alpha\sqrt{r-r'}}\,\rho(X-r')\,dr'\right]=\frac{ik}{\alpha}\cos\theta\left\{\frac{\rho(X)}{\sqrt r}+\int_0^r\frac{e^{ikSr'}}{\sqrt{r-r'}}\Big[ikS\rho(X-r')-\rho'(X-r')\Big]dr'\right\},$$
--   where $\rho'(X-r')=d\rho(X-r')/dX$. The left side is the second expression in eq. (28) for $\langle h(X)\,\partial I(r)/\partial r\rangle$, and the right side is eq. (36).
--
--   **Formalization Note** The statement covers the evaluation of the derivative, eqs. (29) to (36). The first equality in (28) moves the ensemble average inside $d/dr$ and the integral of eq. (24). It is not formalized, because the paper states no regularity of the random surface under which that interchange holds. "$\rho$ may be assumed to be differentiable" is taken as $\rho\in C^1$. The paper's derivation expands $\rho(X-r'-\epsilon)$ to first order in $\epsilon$ uniformly under the integral, which is what $C^1$ provides.
-- source:
--   M. Spivack and O. Rath Spivack, Rough surface backscatter and statistics via extended parabolic integral equation, arXiv:1408.1879v2 (2015), claim c011; Section 4.2, eqs. (28)-(36), PDF pp. 9-11

import Mathlib
import Definitions.Def_Arxiv1408_1879_Basic

open MeasureTheory Filter Topology

namespace Arxiv1408_1879

theorem height_correlation_derivative (k θ X r : ℝ) (hk : 0 < k) (hr : 0 < r) (ρ : ℝ → ℝ)
    (hρ : ContDiff ℝ 1 ρ) :
    Complex.I * k * Real.cos θ * deriv (fun s : ℝ => ∫ r' in (0 : ℝ)..s,
        Complex.exp (Complex.I * ((k * S θ * r' : ℝ) : ℂ)) /
          (alpha k * ((Real.sqrt (s - r') : ℝ) : ℂ)) * (ρ (X - r') : ℂ)) r =
      Complex.I * k / alpha k * Real.cos θ *
        ((ρ X : ℂ) / ((Real.sqrt r : ℝ) : ℂ) + ∫ r' in (0 : ℝ)..r,
          Complex.exp (Complex.I * ((k * S θ * r' : ℝ) : ℂ)) / ((Real.sqrt (r - r') : ℝ) : ℂ) *
            (Complex.I * k * S θ * (ρ (X - r') : ℂ) - ((deriv ρ (X - r') : ℝ) : ℂ))) := by sorry

end Arxiv1408_1879
