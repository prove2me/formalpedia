-- Prove2me | Theorems.Thm_Arxiv1310_4241_pec_debye_sources_decouple
-- name    : Arxiv1310_4241.pec_debye_sources_decouple
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:24:58.484001+00:00
-- url     : https://prove2.me/theorems/d5e93d46-be19-4642-8267-980276c6cdc5
-- title:
--   Eq. (43): the generalized Debye sources on a perfectly conducting half-space decouple at every frequency
-- statement:
--   Let $k=\omega\sqrt{\varepsilon\mu}$ with $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$, let $(\xi,\eta)\ne(0,0)$ with $\beta=\sqrt{\xi^2+\eta^2-k^2}\ne0$, and let the incoming field have $\mathcal S_0\nabla\cdot\mathbf E^{\rm in}=a\,e^{i(\xi x+\eta y)}$ and $\mathbf n\cdot\mathbf H^{\rm in}=b\,e^{i(\xi x+\eta y)}$ on $z=0$, so $a=\mathcal F[\mathcal S_0\nabla\cdot\mathbf E^{\rm in}](\xi,\eta)$ and $b=\mathcal F[\mathbf n\cdot\mathbf H^{\rm in}](\xi,\eta)$. The scattered generalized Debye field of the sources $\widehat r,\widehat q$ on this mode satisfies the boundary conditions $\mathcal S_0\nabla\cdot\mathbf E^{\rm tot}=0$ and $\mathbf n\cdot\mathbf H^{\rm tot}=0$ on $z=0$ if and only if
--
--   $$\widehat r=-\frac{64\pi^4}{\sqrt\mu}\,a\,\frac{\sqrt{\xi^2+\eta^2}}{\beta-ik},\qquad \widehat q=-\frac{8\pi^2}{\sqrt\varepsilon}\,b\,\frac{\beta}{\beta-ik}.$$
--
--   So $\widehat r$ depends only on the incoming electric field and $\widehat q$ only on the incoming magnetic field, at every frequency.
--
--   **Formalization Note** One Fourier mode, as in eq. (42). The condition on $\mathbf E^{\rm tot}$ is $\mathcal S_0$ applied to the divergence of its tangential part, as defined in eq. (38) and used in (42)-(44).
-- source:
--   M. O'Neil, A generalized Debye source approach to electromagnetic scattering in layered media, arXiv:1310.4241v1 (2013), claim c016; Section V.A, eq. (43), PDF p. 11; boundary conditions eqs. (36), (38), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology

namespace Arxiv1310_4241

theorem pec_debye_sources_decouple (ω : ℝ) (ε μ k : ℂ) (hkdef : k = wavenumber ω ε μ)
    (hk : IsCausalWavenumber k) (ξ η : ℝ) (hξη : (ξ, η) ≠ (0, 0))
    (hβ : sommerfeldRoot k ξ η ≠ 0) (a b r q : ℂ) :
    (∀ x y : ℝ,
      laplaceSingleLayerOnMode ξ η (tangentialDivergence (pecE ω ε μ ξ η r q)) (pt x y 0) +
          a * planeWave ξ η x y = 0 ∧
        pecH ω ε μ ξ η r q (pt x y 0) 2 + b * planeWave ξ η x y = 0) ↔
    (r = -(64 * Real.pi ^ 4 / csqrt μ) * a * (Real.sqrt (ξ ^ 2 + η ^ 2) : ℂ) /
        (sommerfeldRoot k ξ η - Complex.I * k) ∧
      q = -(8 * Real.pi ^ 2 / csqrt ε) * b * sommerfeldRoot k ξ η /
        (sommerfeldRoot k ξ η - Complex.I * k)) := by sorry

end Arxiv1310_4241
