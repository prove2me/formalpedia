-- Prove2me | Theorems.Thm_BoltzmannBGK_maxwellian_isBGKSolution
-- name    : BoltzmannBGK.maxwellian_isBGKSolution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:21:26.819188+00:00
-- url     : https://prove2.me/theorems/2bf454a9-7896-4a06-8fa4-c23b0b9fe764
-- title:
--   Maxwellians are equilibrium solutions of the BGK equation
-- statement:
--   Let $\tau>0$, $\rho>0$, $\theta>0$ and $u\in\mathbb R^3$. The field that is constant in time and position and equal to the Maxwellian $M_{\rho,u,\theta}$ in velocity,
--
--   $$f(x,v,t)=M_{\rho,u,\theta}(v),$$
--
--   solves the Boltzmann equation with the BGK collision operator,
--
--   $$\frac{\partial f}{\partial t}+v\cdot\nabla_x f=C[f].$$
--
--   Both transport terms vanish because $f$ does not depend on $t$ or $x$, and the collision term vanishes because a Maxwellian is its own local Maxwellian. Thus the global Maxwellians are exact equilibrium solutions of the model — the states towards which the $H$-theorem drives the gas.
--
--   **Formalization Note** Solving the equation here includes the differentiability of the field in $t$ and in $x$, which is part of the definition of a solution.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (a) and equation (*): the BGK equation and its Maxwellian equilibria.

import Definitions.Def_BoltzmannBGK_model

open MeasureTheory Real

namespace BoltzmannBGK

theorem maxwellian_isBGKSolution (τ ρ θ : ℝ) (u : Vel) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hθ : 0 < θ) :
    IsBGKSolution τ fun _ _ v => maxwellian ρ u θ v := by sorry

end BoltzmannBGK
