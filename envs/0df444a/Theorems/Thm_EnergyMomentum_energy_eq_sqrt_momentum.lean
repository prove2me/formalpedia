-- Prove2me | Theorems.Thm_EnergyMomentum_energy_eq_sqrt_momentum
-- name    : EnergyMomentum.energy_eq_sqrt_momentum
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:11:41.778197+00:00
-- url     : https://prove2.me/theorems/2a7d5f57-f795-47a7-8212-b7404a0b07f7
-- title:
--   Energy in terms of momentum: $E = mc^2\sqrt{1 + (p/mc)^2}$
-- statement:
--   Let $c > 0$, $m > 0$ and $\mathbf v\in\mathbb R^3$ with $|\mathbf v| < c$. The total energy $E = \gamma mc^2$ and the momentum magnitude $p = |\gamma m \mathbf v|$ satisfy
--
--   $$
--   E = mc^2\sqrt{1 + \left(\frac{p}{mc}\right)^2}.
--   $$
--
--   Squaring both sides and rearranging yields the energy–momentum relation (1).
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer), §Origins and derivation of the equation → Heuristic approach for massive particles; also §Classical correspondence (first display).

import Mathlib
import Definitions.Def_EnergyMomentum_basic

namespace EnergyMomentum

/-- Energy in terms of three-momentum: `E = m c² √(1 + (p / (m c))²)`. -/
theorem energy_eq_sqrt_momentum (m c : ℝ) (v : Vec3)
    (hc : 0 < c) (hm : 0 < m) (hv : ‖v‖ < c) :
    energy m c v = m * c ^ 2 * Real.sqrt (1 + (‖momentum m c v‖ / (m * c)) ^ 2) := by sorry

end EnergyMomentum
