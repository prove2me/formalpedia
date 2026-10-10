-- Prove2me | Theorems.Thm_EnergyMomentum_energy_momentum_relation
-- name    : EnergyMomentum.energy_momentum_relation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:20:38.091979+00:00
-- url     : https://prove2.me/theorems/d8878335-bf03-4f15-9ce9-586cfede0296
-- title:
--   Energy–momentum relation $E^2 = (pc)^2 + (mc^2)^2$
-- statement:
--   Let $c > 0$ be the speed of light and consider a free body of mass $m > 0$ moving with velocity $\mathbf v \in \mathbb R^3$ with $|\mathbf v| < c$. Let $E = \gamma m c^2$ be its total energy and $\mathbf p = \gamma m \mathbf v$ its relativistic momentum, where $\gamma = 1/\sqrt{1-(|\mathbf v|/c)^2}$. Then, with $p = |\mathbf p|$,
--
--   $$
--   E^2 = (pc)^2 + (mc^2)^2 .
--   $$
--
--   This is the relativistic dispersion relation; it expresses the energy through the momentum and the rest mass alone and extends $E_0 = mc^2$ to moving bodies.
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer), lead section, equation (1).

import Mathlib
import Definitions.Def_EnergyMomentum_basic

namespace EnergyMomentum

/-- Energy–momentum relation (1): `E² = (p c)² + (m c²)²` for a free massive body. -/
theorem energy_momentum_relation (m c : ℝ) (v : Vec3)
    (hc : 0 < c) (hm : 0 < m) (hv : ‖v‖ < c) :
    energy m c v ^ 2 = (‖momentum m c v‖ * c) ^ 2 + (m * c ^ 2) ^ 2 := by sorry

end EnergyMomentum
