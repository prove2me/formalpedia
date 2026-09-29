-- Prove2me | Theorems.Thm_BoltzmannBGK_reduceH_maxwellianSlab
-- name    : BoltzmannBGK.reduceH_maxwellianSlab
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:26:27.234893+00:00
-- url     : https://prove2.me/theorems/da50d2c9-df18-4a22-aaf4-1d0f62526f7a
-- title:
--   Reduced equilibrium $h^{(0)}=2\theta g^{(0)}$
-- statement:
--   In the slab geometry of part (c), with $v=(v,v_\perp)$, $u=(u,0,0)$ and
--
--   $$f^{(0)}(v,v_\perp)=\frac{\rho}{(2\pi\theta)^{3/2}}\exp\Big(-\frac{(v-u)^2+|v_\perp|^2}{2\theta}\Big),$$
--
--   let $\theta>0$. Weighting by the perpendicular kinetic energy before integrating out $v_\perp$ gives
--
--   $$h^{(0)}(v)=\int_{\mathbb R^2}\mathrm dv_\perp\,|v_\perp|^2 f^{(0)}(v,v_\perp)=2\theta\,g^{(0)}(v),$$
--
--   where $g^{(0)}(v)=\rho(2\pi\theta)^{-1/2}\exp\big(-(v-u)^2/2\theta\big)$ is the one-dimensional Maxwellian.
--
--   The factor $2\theta$ is the mean perpendicular kinetic energy per particle: two transverse degrees of freedom, each contributing $\theta$. This determines the second equilibrium of the closed system $(\dagger)$ of part (c).
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (c), determination of h^{(0)}.

import Definitions.Def_BoltzmannBGK_slab

open MeasureTheory Real

namespace BoltzmannBGK

theorem reduceH_maxwellianSlab (ρ u θ : ℝ) (hθ : 0 < θ) :
    reduceH (maxwellianSlab ρ u θ) = fun w => 2 * θ * maxwellian1d ρ u θ w := by sorry

end BoltzmannBGK
