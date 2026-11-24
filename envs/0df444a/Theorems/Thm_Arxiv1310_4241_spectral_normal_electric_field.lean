-- Prove2me | Theorems.Thm_Arxiv1310_4241_spectral_normal_electric_field
-- name    : Arxiv1310_4241.spectral_normal_electric_field
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:22:36.726366+00:00
-- url     : https://prove2.me/theorems/0a7e6d84-fafe-440c-99e5-9919df877159
-- title:
--   Eq. (27): the normal electric field of a current below the plane
-- statement:
--   Let $k=\omega\sqrt{\varepsilon\mu}$ with $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$, and $\beta=\sqrt{\xi^2+\eta^2-k^2}$ as in (9). Let $\mathbf J$ be a $C^1$ current with compact support in $z<0$, and let $\rho$ be the charge density, $\nabla\cdot\mathbf J=i\omega\rho$ (eq. (2)). Let $\mathbf E$ be the Lorenz-gauge electric field of eq. (6). Then for every $\mathbf x$ with $z>0$,
--
--   $$E_z(\mathbf x)=\int_{\mathbb R^2}\widehat g_k(\xi,\eta,z)\Big(\int e^{\beta z'}\Big[i\omega\mu J_z(\mathbf x')+\frac{\beta}{\varepsilon}\rho(\mathbf x')\Big]e^{-i(\xi x'+\eta y')}\,dV'\Big)e^{i(\xi x+\eta y)}\,d\xi\,d\eta.$$
--
--   The paper prints this formula without derivation.
-- source:
--   M. O'Neil, A generalized Debye source approach to electromagnetic scattering in layered media, arXiv:1310.4241v1 (2013), claim c005; Section IV, eq. (27), PDF p. 8; Lorenz gauge eq. (6), PDF p. 3; continuity condition eq. (2), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology

namespace Arxiv1310_4241

theorem spectral_normal_electric_field (ω : ℝ) (ε μ k : ℂ) (hkdef : k = wavenumber ω ε μ)
    (hk : IsCausalWavenumber k) (J : Space → Fin 3 → ℂ) (ρ : Space → ℂ) (hJ : ContDiff ℝ 1 J)
    (hJc : HasCompactSupport J) (hJV : tsupport J ⊆ {q : Space | q 2 < 0})
    (hcont : ∀ q, divergence J q = Complex.I * ω * ρ q) (p : Space) (hp : 0 < p 2) :
    lorenzE ω ε μ J p 2 = ∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 (p 2) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) *
          (Complex.I * ω * μ * J q 2 + sommerfeldRoot k ζ.1 ζ.2 / ε * ρ q) *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p 0) (p 1) := by sorry

end Arxiv1310_4241
