-- Prove2me | Theorems.Thm_BoltzmannBGK_maxwellian_energy
-- name    : BoltzmannBGK.maxwellian_energy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:17:12.359324+00:00
-- url     : https://prove2.me/theorems/1d079865-2273-46c5-b15b-99a227f86e7d
-- title:
--   Central second moment: $\int |v-u|^2 M_{\rho,u,\theta}\,\mathrm dv=3\rho\theta$
-- statement:
--   Let $\theta>0$, let $\rho\in\mathbb R$ and let $u\in\mathbb R^3$. The second moment of the Maxwellian $M_{\rho,u,\theta}$ about its bulk velocity is
--
--   $$\int_{\mathbb R^3}|v-u|^2\,M_{\rho,u,\theta}(v)\,\mathrm dv=3\rho\theta .$$
--
--   Since the particles have unit mass and the Boltzmann constant is set to $1$, the left-hand side is twice the internal energy density, so this identity is the statement that the parameter $\theta$ is the temperature of the Maxwellian: the energy per particle is $\tfrac32\theta$, one half per degree of freedom.
--
--   **Formalization Note** The moment is taken about $u$, not about the origin; the corresponding identity about the origin differs by $\rho|u|^2$.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (a), the interpretation of theta.

import Definitions.Def_BoltzmannBGK_model

open MeasureTheory Real

namespace BoltzmannBGK

theorem maxwellian_energy (ρ θ : ℝ) (u : Vel) (hθ : 0 < θ) :
    ∫ v, ‖v - u‖ ^ 2 * maxwellian ρ u θ v = 3 * ρ * θ := by sorry

end BoltzmannBGK
