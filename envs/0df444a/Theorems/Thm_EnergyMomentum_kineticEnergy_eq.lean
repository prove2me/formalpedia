-- Prove2me | Theorems.Thm_EnergyMomentum_kineticEnergy_eq
-- name    : EnergyMomentum.kineticEnergy_eq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:14:19.752234+00:00
-- url     : https://prove2.me/theorems/8c42994c-1f6a-4ad7-96a4-81b575dc1a31
-- title:
--   Relativistic kinetic energy $E_K = \sqrt{(pc)^2 + (mc^2)^2} - mc^2$
-- statement:
--   Let $c>0$, $m>0$ and $\mathbf v\in\mathbb R^3$ with $|\mathbf v|<c$. The relativistic kinetic energy $E_K = E - E_0$, the difference between the total energy $E = \gamma mc^2$ and the rest energy $E_0 = mc^2$, satisfies
--
--   $$
--   E_K = \sqrt{(pc)^2 + (mc^2)^2} - mc^2 ,
--   $$
--
--   where $p = |\gamma m\mathbf v|$.
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer), lead section (display following equation (1)).

import Mathlib
import Definitions.Def_EnergyMomentum_basic

namespace EnergyMomentum

/-- Relativistic kinetic energy: `E_K = E − E₀ = √((p c)² + (m c²)²) − m c²`. -/
theorem kineticEnergy_eq (m c : ℝ) (v : Vec3)
    (hc : 0 < c) (hm : 0 < m) (hv : ‖v‖ < c) :
    kineticEnergy m c v
      = Real.sqrt ((‖momentum m c v‖ * c) ^ 2 + (m * c ^ 2) ^ 2) - m * c ^ 2 := by sorry

end EnergyMomentum
