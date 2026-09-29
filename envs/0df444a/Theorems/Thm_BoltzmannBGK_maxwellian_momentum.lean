-- Prove2me | Theorems.Thm_BoltzmannBGK_maxwellian_momentum
-- name    : BoltzmannBGK.maxwellian_momentum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:16:40.487552+00:00
-- url     : https://prove2.me/theorems/e93c9848-fe31-4322-8389-aac9f576806c
-- title:
--   First moment of the Maxwellian: $\int v\,M_{\rho,u,\theta}\,\mathrm dv=\rho u$
-- statement:
--   Let $\theta>0$, let $\rho\in\mathbb R$ and let $u\in\mathbb R^3$. The first velocity moment of the Maxwellian $M_{\rho,u,\theta}$ is the momentum density $\rho u$:
--
--   $$\int_{\mathbb R^3} v\,M_{\rho,u,\theta}(v)\,\mathrm dv=\rho\,u .$$
--
--   This identifies the parameter $u$ as the bulk velocity of the Maxwellian, and is the second of the three moment identities behind the conservation laws of part (a) of the source question.
--
--   **Formalization Note** Both sides are vectors in $\mathbb R^3$; the left-hand side is a vector-valued (Bochner) integral, written as the integral of the scalar $M_{\rho,u,\theta}(v)$ scaling the vector $v$.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (a), the interpretation of u.

import Definitions.Def_BoltzmannBGK_model

open MeasureTheory Real

namespace BoltzmannBGK

theorem maxwellian_momentum (ρ θ : ℝ) (u : Vel) (hθ : 0 < θ) :
    ∫ v, maxwellian ρ u θ v • v = ρ • u := by sorry

end BoltzmannBGK
