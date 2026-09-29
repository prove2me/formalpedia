-- Prove2me | Theorems.Thm_BoltzmannConstant_equipartition_per_degree_of_freedom
-- name    : BoltzmannConstant.equipartition_per_degree_of_freedom
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T14:07:26.014245+00:00
-- url     : https://prove2.me/theorems/583fd0cb-6c04-43d3-bc1a-6aca75ac2be2
-- title:
--   Equipartition: $\tfrac{1}{2}k_BT$ per translational degree of freedom
-- statement:
--   The velocity vector has three degrees of freedom, one per spatial direction, so $\langle v^2 \rangle = \langle v_x^2 \rangle + \langle v_y^2 \rangle + \langle v_z^2 \rangle$ with the three contributions equal by isotropy. Given that the mean translational kinetic energy is $\tfrac{1}{2}m\langle v^2\rangle = \tfrac{3}{2}k_BT$, the average energy per degree of freedom is one third of that, $$\tfrac{1}{2} m \langle v_x^2 \rangle = \tfrac{1}{2} k_B T,$$ which is the equipartition statement that each microscopic degree of freedom carries $\tfrac{1}{2}k_BT$.
-- source:
--   Wikipedia, "Boltzmann constant" (uploaded PDF), https://en.wikipedia.org/wiki/Boltzmann_constant, section "Role in the equipartition of energy" (average energy per degree of freedom equal to $\tfrac{1}{2}kT$)

import Mathlib
import Definitions.Def_boltzmann_si_basics

namespace BoltzmannConstant

theorem equipartition_per_degree_of_freedom
    (m T vx2 vy2 vz2 msq : ℝ) (hsum : msq = vx2 + vy2 + vz2)
    (hxy : vx2 = vy2) (hyz : vy2 = vz2)
    (hmean : m * msq / 2 = 3 / 2 * (kB * T)) :
    m * vx2 / 2 = kB * T / 2 := by sorry

end BoltzmannConstant
