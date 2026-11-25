-- Prove2me | Theorems.Thm_Arxiv2111_09089_cayley_nonuniform_sampling
-- name    : Arxiv2111_09089.cayley_nonuniform_sampling
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T10:31:25.13119+00:00
-- url     : https://prove2.me/theorems/0a2395be-fafe-5fff-b41c-257df9da3bfa
-- title:
--   Section II-C, first benefit of eq. (3): non-uniform sampling of the real $\mu$ axis
-- statement:
--   On the unit circle $\eta=e^{j\phi}$, $0<\phi<2\pi$, the Cayley transform $\mu(\eta)=-j(1+\eta)/(1-\eta)$ is
--
--   $$\mu(e^{j\phi})=\cot(\phi/2).$$
--
--   The map $\phi\mapsto\cot(\phi/2)$ is strictly decreasing on $(0,2\pi)$. It tends to $+\infty$ as $\phi\to0^+$ and to $-\infty$ as $\phi\to2\pi^-$, so it covers the entire real $\mu$ axis. Its derivative is
--
--   $$\frac{d\mu}{d\phi}=-\frac{1+\mu^2}{2}.$$
--
--   Hence samples uniformly spaced in $\phi$ (as used by the FFT) are spaced $\approx\frac{1+\mu^2}{2}\Delta\phi$ apart in $\mu$. They are densest at $\mu=0$ and become dilute as $\mu\to\pm\infty$.
--
--   **Formalization Note** The paper states the non-uniform sampling qualitatively. It is formalised as the exact formula for $\mu$ on the circle, its monotonicity and range, and its derivative, from which the spacing of uniform samples follows.
-- source:
--   Y. Hadad, On the use of the Padé-Fourier approximation in fast evaluation of the Green's function of layered media, arXiv:2111.09089v1 (2021), claim c023; Section II-C, paragraph after eq. (3), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

open Complex MeasureTheory Filter Topology Asymptotics

namespace Arxiv2111_09089

theorem cayley_nonuniform_sampling :
    (∀ φ ∈ Set.Ioo 0 (2 * Real.pi), cayley (exp ((φ : ℂ) * I)) = (Real.cot (φ / 2) : ℂ)) ∧
    StrictAntiOn (fun φ : ℝ => Real.cot (φ / 2)) (Set.Ioo 0 (2 * Real.pi)) ∧
    Tendsto (fun φ : ℝ => Real.cot (φ / 2)) (𝓝[>] 0) atTop ∧
    Tendsto (fun φ : ℝ => Real.cot (φ / 2)) (𝓝[<] (2 * Real.pi)) atBot ∧
    ∀ φ ∈ Set.Ioo 0 (2 * Real.pi),
      HasDerivAt (fun ψ : ℝ => Real.cot (ψ / 2)) (-(1 + Real.cot (φ / 2) ^ 2) / 2) φ := by sorry

end Arxiv2111_09089
