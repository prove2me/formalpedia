-- Prove2me | Theorems.Thm_Arxiv1310_4241_pec_debye_sources_low_frequency
-- name    : Arxiv1310_4241.pec_debye_sources_low_frequency
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:25:22.726528+00:00
-- url     : https://prove2.me/theorems/7ed72161-82a4-4ef5-b908-d6b228d4d7b6
-- title:
--   Eq. (44): the Debye sources of (43) are stable as $\omega\to0$ and reduce to (44) at $\omega=0$
-- statement:
--   Let $\varepsilon,\mu\in\mathbb C$ be such that $k(\omega)=\omega\sqrt{\varepsilon\mu}$ satisfies $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$ for every $\omega>0$, let $(\xi,\eta)\ne(0,0)$ and $a,b\in\mathbb C$ as in eq. (43). Then:
--
--   1. As $\omega\to0^+$, the right-hand sides of (43) converge to those of (44):
--   $$-\frac{64\pi^4}{\sqrt\mu}a\frac{\sqrt{\xi^2+\eta^2}}{\beta-ik}\to-\frac{64\pi^4}{\sqrt\mu}a,\qquad -\frac{8\pi^2}{\sqrt\varepsilon}b\frac{\beta}{\beta-ik}\to-\frac{8\pi^2}{\sqrt\varepsilon}b.$$
--   2. At $\omega=0$ the boundary conditions $\mathcal S_0\nabla\cdot\mathbf E^{\rm tot}=0$, $\mathbf n\cdot\mathbf H^{\rm tot}=0$ on the mode hold if and only if
--   $$\widehat r=-\frac{64\pi^4}{\sqrt\mu}\,a,\qquad \widehat q=-\frac{8\pi^2}{\sqrt\varepsilon}\,b,$$
--   which is eq. (44), the analogue of a Neumann problem on a half-space.
--
--   **Formalization Note** "Stable as $\omega\to0$" is stated as convergence, for each mode, of the coefficients of (43) to the finite values (44). At $\omega=0$ the standing assumption $\operatorname{Re}k>0$ fails; the paper evaluates the formulas there anyway, and so does part 2.
-- source:
--   M. O'Neil, A generalized Debye source approach to electromagnetic scattering in layered media, arXiv:1310.4241v1 (2013), claim c017; Section V.A, eqs. (43)-(44), PDF p. 11

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology

namespace Arxiv1310_4241

theorem pec_debye_sources_low_frequency (ε μ : ℂ)
    (hk : ∀ ω : ℝ, 0 < ω → IsCausalWavenumber (wavenumber ω ε μ)) (ξ η : ℝ)
    (hξη : (ξ, η) ≠ (0, 0)) (a b : ℂ) :
    Tendsto (fun ω : ℝ => -(64 * Real.pi ^ 4 / csqrt μ) * a * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) /
        (sommerfeldRoot (wavenumber ω ε μ) ξ η - Complex.I * wavenumber ω ε μ))
      (𝓝[>] 0) (𝓝 (-(64 * Real.pi ^ 4 / csqrt μ) * a)) ∧
    Tendsto (fun ω : ℝ => -(8 * Real.pi ^ 2 / csqrt ε) * b * sommerfeldRoot (wavenumber ω ε μ) ξ η /
        (sommerfeldRoot (wavenumber ω ε μ) ξ η - Complex.I * wavenumber ω ε μ))
      (𝓝[>] 0) (𝓝 (-(8 * Real.pi ^ 2 / csqrt ε) * b)) ∧
    ∀ r q : ℂ,
      ((∀ x y : ℝ,
        laplaceSingleLayerOnMode ξ η (tangentialDivergence (pecE 0 ε μ ξ η r q)) (pt x y 0) +
            a * planeWave ξ η x y = 0 ∧
          pecH 0 ε μ ξ η r q (pt x y 0) 2 + b * planeWave ξ η x y = 0) ↔
      (r = -(64 * Real.pi ^ 4 / csqrt μ) * a ∧ q = -(8 * Real.pi ^ 2 / csqrt ε) * b)) := by sorry

end Arxiv1310_4241
