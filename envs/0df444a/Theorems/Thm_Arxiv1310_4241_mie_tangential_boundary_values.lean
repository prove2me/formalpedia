-- Prove2me | Theorems.Thm_Arxiv1310_4241_mie_tangential_boundary_values
-- name    : Arxiv1310_4241.mie_tangential_boundary_values
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T11:23:13.38494+00:00
-- url     : https://prove2.me/theorems/e4608728-4b0e-4dc6-8274-b22b371ad9c3
-- title:
--   Eq. (29) (as derived): the electric field of the planar Mie representation on $z=0$
-- statement:
--   Let $k=\omega\sqrt{\varepsilon\mu}$ with $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$, $\beta=\sqrt{\xi^2+\eta^2-k^2}$ as in (9), and let $\widehat\sigma,\widehat\tau$ be measurable spectral densities with
--
--   $$\int_{\mathbb R^2}(1+\xi^2+\eta^2)\,|\widehat g_k(\xi,\eta,0)|\,\big(|\widehat\sigma|+|\widehat\tau|\big)\,d\xi\,d\eta<\infty.$$
--
--   Let $u,v$ be the Debye potentials (24) of $\widehat\sigma,\widehat\tau$ and $\mathbf E$ the field (22). Then, as $z\to0^+$,
--
--   $$E_x(x,y,z)\to\int\widehat g_k(\xi,\eta,0)\big(-i\xi\beta\,\widehat\sigma-\omega\mu\eta\,\widehat\tau\big)e^{i(\xi x+\eta y)}\,d\xi\,d\eta,$$
--
--   $$E_y(x,y,z)\to\int\widehat g_k(\xi,\eta,0)\big(-i\eta\beta\,\widehat\sigma+\omega\mu\xi\,\widehat\tau\big)e^{i(\xi x+\eta y)}\,d\xi\,d\eta,$$
--
--   $$E_z(x,y,z)\to\int\widehat g_k(\xi,\eta,0)(\xi^2+\eta^2)\,\widehat\sigma\,e^{i(\xi x+\eta y)}\,d\xi\,d\eta.$$
--
--   **Formalization Note** This is eq. (29) as it follows from (22) and (24): the $\widehat\sigma$-terms of $E_x$ and $E_y$ carry $-i\xi\beta$ and $-i\eta\beta$, opposite to the printed $+i\xi\beta$, $+i\eta\beta$, because $\partial_z$ acts on $e^{-\beta z}$ as $-\beta$. The values on $z=0$ are read as limits from $z>0$. The integrability condition is the condition, not stated in the paper, under which (24) and its second derivatives converge absolutely.
-- source:
--   M. O'Neil, A generalized Debye source approach to electromagnetic scattering in layered media, arXiv:1310.4241v1 (2013), claim c007; Section IV, eq. (29), PDF p. 8; representation eqs. (22), (24), PDF p. 7

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology

namespace Arxiv1310_4241

theorem mie_tangential_boundary_values (ω : ℝ) (ε μ k : ℂ) (hkdef : k = wavenumber ω ε μ)
    (hk : IsCausalWavenumber k) (σh τh : ℝ × ℝ → ℂ)
    (hσm : AEStronglyMeasurable σh volume) (hτm : AEStronglyMeasurable τh volume)
    (hσ : Integrable (fun ζ : ℝ × ℝ => (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖σh ζ‖))
    (hτ : Integrable (fun ζ : ℝ × ℝ => (1 + ζ.1 ^ 2 + ζ.2 ^ 2) * ‖ghat k ζ.1 ζ.2 0‖ * ‖τh ζ‖))
    (x y : ℝ) :
    Tendsto (fun z => mieE ω μ (debyePotential k σh) (debyePotential k τh) (pt x y z) 0)
      (𝓝[>] 0) (𝓝 (∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 0 *
        (-(Complex.I * ζ.1 * sommerfeldRoot k ζ.1 ζ.2 * σh ζ) - ω * μ * ζ.2 * τh ζ) *
        planeWave ζ.1 ζ.2 x y)) ∧
    Tendsto (fun z => mieE ω μ (debyePotential k σh) (debyePotential k τh) (pt x y z) 1)
      (𝓝[>] 0) (𝓝 (∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 0 *
        (-(Complex.I * ζ.2 * sommerfeldRoot k ζ.1 ζ.2 * σh ζ) + ω * μ * ζ.1 * τh ζ) *
        planeWave ζ.1 ζ.2 x y)) ∧
    Tendsto (fun z => mieE ω μ (debyePotential k σh) (debyePotential k τh) (pt x y z) 2)
      (𝓝[>] 0) (𝓝 (∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 0 * ((ζ.1 : ℂ) ^ 2 + (ζ.2 : ℂ) ^ 2) * σh ζ *
        planeWave ζ.1 ζ.2 x y)) := by sorry

end Arxiv1310_4241
