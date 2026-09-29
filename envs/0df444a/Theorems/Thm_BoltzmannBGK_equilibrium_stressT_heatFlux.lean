-- Prove2me | Theorems.Thm_BoltzmannBGK_equilibrium_stressT_heatFlux
-- name    : BoltzmannBGK.equilibrium_stressT_heatFlux
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:28:08.212983+00:00
-- url     : https://prove2.me/theorems/37869699-b779-49e0-a8cf-247726db1a07
-- title:
--   $T$ and $q$ vanish at the reduced equilibrium
-- statement:
--   Part (d) of the source question writes the momentum and energy fluxes of the reduced system in terms of $\rho$, $u$, $\theta$ and the two further quantities
--
--   $$T=-2\rho\theta+\int\mathrm dv\,h,\qquad q=\frac12\int\mathrm dv\,w^3g+\frac12\int\mathrm dv\,w\,h,$$
--
--   where $w=v-u$ is the peculiar velocity: $T$ measures the anisotropy of the pressure (the difference between the transverse and longitudinal pressures, a deviatoric stress), and $q$ is the heat flux.
--
--   Let $\rho>0$ and $\theta>0$. Evaluated on the equilibrium pair $g=g^{(0)}$, $h=h^{(0)}=2\theta g^{(0)}$, both quantities vanish:
--
--   $$T=0,\qquad q=0 .$$
--
--   For $T$ this is the isotropy of the Maxwellian pressure, $\int h^{(0)}\,\mathrm dv=2\rho\theta$; for $q$ it is the symmetry of $g^{(0)}$ and $h^{(0)}$ about $v=u$, which kills both odd moments. Consequently the reduced equations close on the Euler system precisely when the gas is in local equilibrium, and $T$ and $q$ measure the departure from it.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (d), the quantities T and q and their vanishing at equilibrium.

import Definitions.Def_BoltzmannBGK_slab

open MeasureTheory Real

namespace BoltzmannBGK

theorem equilibrium_stressT_heatFlux (ρ u θ : ℝ) (hρ : 0 < ρ) (hθ : 0 < θ) :
    stressT (maxwellian1d ρ u θ) (fun w => 2 * θ * maxwellian1d ρ u θ w) = 0 ∧
      heatFlux (maxwellian1d ρ u θ) (fun w => 2 * θ * maxwellian1d ρ u θ w) = 0 := by
  sorry

end BoltzmannBGK
