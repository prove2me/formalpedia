-- Prove2me | Theorems.Thm_BoltzmannBGK_maxwellian1d_moments
-- name    : BoltzmannBGK.maxwellian1d_moments
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:27:26.835877+00:00
-- url     : https://prove2.me/theorems/76b7ccc9-a701-4766-be25-47de668122c2
-- title:
--   $\rho$, $u$, $\theta$ of the reduced equilibrium $(g^{(0)},h^{(0)})$
-- statement:
--   In the reduced system $(\dagger)$ of part (c) the macroscopic quantities are expressed through the two fields $g$ and $h$ by
--
--   $$\rho=\int\mathrm dv\,g,\qquad u=\frac1\rho\int\mathrm dv\,v\,g,\qquad 3\rho\theta=\int\mathrm dv\,(v-u)^2g+\int\mathrm dv\,h .$$
--
--   Let $\rho>0$ and $\theta>0$. Evaluating these three expressions on the reduced equilibrium pair
--
--   $$g^{(0)}(v)=\frac{\rho}{(2\pi\theta)^{1/2}}\exp\Big(-\frac{(v-u)^2}{2\theta}\Big),\qquad h^{(0)}=2\theta\,g^{(0)},$$
--
--   returns the parameters themselves: the density is $\rho$, the bulk velocity is $u$, and the temperature is $\theta$. The longitudinal degree of freedom contributes $\rho\theta$ to the energy integral and the two transverse ones contribute $2\rho\theta$, together giving $3\rho\theta$.
--
--   This confirms that the expressions for $\rho$, $u$ and $\theta$ in the reduced system are consistent with the three-dimensional definitions.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (c), expressions for rho, u, theta in the reduced system.

import Definitions.Def_BoltzmannBGK_slab

open MeasureTheory Real

namespace BoltzmannBGK

theorem maxwellian1d_moments (ρ u θ : ℝ) (hρ : 0 < ρ) (hθ : 0 < θ) :
    density1d (maxwellian1d ρ u θ) = ρ ∧
      bulkVelocity1d (maxwellian1d ρ u θ) = u ∧
      temperature1d (maxwellian1d ρ u θ) (fun w => 2 * θ * maxwellian1d ρ u θ w) = θ := by
  sorry

end BoltzmannBGK
