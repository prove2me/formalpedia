-- Prove2me | Theorems.Thm_BoltzmannBGK_reduceG_maxwellianSlab
-- name    : BoltzmannBGK.reduceG_maxwellianSlab
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:24:23.660111+00:00
-- url     : https://prove2.me/theorems/19639960-c383-4799-8d83-0d5d9bd0c77b
-- title:
--   Reduced equilibrium $g^{(0)}$: $\int \mathrm dv_\perp\,f^{(0)}$
-- statement:
--   In the slab geometry of part (c) of the source question, write $v=(v,v_\perp)$ with $v_\perp=(v_y,v_z)$ and $u=(u,0,0)$, so that the Maxwellian reads
--
--   $$f^{(0)}(v,v_\perp)=\frac{\rho}{(2\pi\theta)^{3/2}}\exp\Big(-\frac{(v-u)^2+|v_\perp|^2}{2\theta}\Big).$$
--
--   Let $\theta>0$. Integrating out the two perpendicular velocity components gives the one-dimensional Maxwellian
--
--   $$g^{(0)}(v)=\int_{\mathbb R^2}\mathrm dv_\perp\,f^{(0)}(v,v_\perp)=\frac{\rho}{(2\pi\theta)^{1/2}}\exp\Big(-\frac{(v-u)^2}{2\theta}\Big).$$
--
--   This identifies the equilibrium $g^{(0)}$ of the reduced system $(\dagger)$ of part (c): the reduced field $g=\int f\,\mathrm dv_\perp$ relaxes towards the one-dimensional Maxwellian carrying the same $\rho$, $u$, $\theta$.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (c), determination of g^{(0)}.

import Definitions.Def_BoltzmannBGK_slab

open MeasureTheory Real

namespace BoltzmannBGK

theorem reduceG_maxwellianSlab (ρ u θ : ℝ) (hθ : 0 < θ) :
    reduceG (maxwellianSlab ρ u θ) = maxwellian1d ρ u θ := by sorry

end BoltzmannBGK
