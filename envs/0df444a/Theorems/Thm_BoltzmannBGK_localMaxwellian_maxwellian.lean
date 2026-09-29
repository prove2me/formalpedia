-- Prove2me | Theorems.Thm_BoltzmannBGK_localMaxwellian_maxwellian
-- name    : BoltzmannBGK.localMaxwellian_maxwellian
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:19:08.421191+00:00
-- url     : https://prove2.me/theorems/8120a0cf-ac1b-4c52-a82a-3869cfe72e55
-- title:
--   A Maxwellian is its own local Maxwellian: $M^{(0)}=M$
-- statement:
--   Let $\rho>0$, $\theta>0$ and $u\in\mathbb R^3$. Reading off the density, bulk velocity and temperature of the Maxwellian $M_{\rho,u,\theta}$ returns exactly the parameters $\rho$, $u$, $\theta$, and hence
--
--   $$\big(M_{\rho,u,\theta}\big)^{(0)}=M_{\rho,u,\theta},$$
--
--   where $f^{(0)}$ denotes the Maxwellian carrying the same three moments as $f$. Equivalently, the BGK collision operator annihilates every Maxwellian: the Maxwellians are exactly the collisional equilibria of the model, which is the fixed-point statement underlying both the $H$-theorem and the existence of equilibrium solutions of the kinetic equation.
--
--   **Formalization Note** Positivity of $\rho$ is needed because the bulk velocity and the temperature are defined by dividing by the density.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (a), the statement that rho, u, theta are the moments of f^{(0)}.

import Definitions.Def_BoltzmannBGK_model

open MeasureTheory Real

namespace BoltzmannBGK

theorem localMaxwellian_maxwellian (ρ θ : ℝ) (u : Vel) (hρ : 0 < ρ) (hθ : 0 < θ) :
    localMaxwellian (maxwellian ρ u θ) = maxwellian ρ u θ := by sorry

end BoltzmannBGK
