-- Prove2me | Theorems.Thm_BoltzmannBGK_maxwellian_integral
-- name    : BoltzmannBGK.maxwellian_integral
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:16:16.798131+00:00
-- url     : https://prove2.me/theorems/3b090e0c-407f-4e53-ab3a-6b45a6f574c4
-- title:
--   Normalisation of the Maxwellian: $\int M_{\rho,u,\theta}\,\mathrm dv=\rho$
-- statement:
--   Let $\theta>0$, let $\rho\in\mathbb R$ and let $u\in\mathbb R^3$, and let
--
--   $$M_{\rho,u,\theta}(v)=\frac{\rho}{(2\pi\theta)^{3/2}}\exp\Big(-\frac{|v-u|^2}{2\theta}\Big)$$
--
--   be the Maxwellian with these parameters. Then its integral over velocity space is the mass density:
--
--   $$\int_{\mathbb R^3} M_{\rho,u,\theta}(v)\,\mathrm dv=\rho .$$
--
--   This is the normalisation of the Gaussian prefactor, and it is the first of the three moment identities that identify $\rho$, $u$ and $\theta$ as the density, bulk velocity and temperature of the Maxwellian. It is used throughout the mission, in particular to show that a Maxwellian is its own local Maxwellian.
--
--   **Formalization Note** The statement is for arbitrary real $\rho$, positive or not, since both sides are linear in $\rho$.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (a), the definition of f^{(0)} and the interpretation of rho.

import Definitions.Def_BoltzmannBGK_model

open MeasureTheory Real

namespace BoltzmannBGK

theorem maxwellian_integral (ρ θ : ℝ) (u : Vel) (hθ : 0 < θ) :
    ∫ v, maxwellian ρ u θ v = ρ := by sorry

end BoltzmannBGK
