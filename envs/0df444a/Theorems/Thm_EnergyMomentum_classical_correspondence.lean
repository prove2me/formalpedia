-- Prove2me | Theorems.Thm_EnergyMomentum_classical_correspondence
-- name    : EnergyMomentum.classical_correspondence
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:14:55.991368+00:00
-- url     : https://prove2.me/theorems/aa72c59e-71f8-4d63-9ab4-85ba1479466d
-- title:
--   Classical correspondence: $E = mc^2 + \tfrac12 mv^2 + o(v^2)$
-- statement:
--   Let $c>0$ and $m>0$. For velocities $\mathbf v\in\mathbb R^3$, the total energy $E(\mathbf v) = \gamma mc^2$ satisfies
--
--   $$
--   \lim_{\mathbf v\to 0,\ \mathbf v\ne 0} \frac{E(\mathbf v) - mc^2 - \tfrac12 m|\mathbf v|^2}{|\mathbf v|^2} = 0 ,
--   $$
--
--   that is, $E = mc^2 + \tfrac12 m|\mathbf v|^2 + o(|\mathbf v|^2)$ as $\mathbf v \to 0$: to first order the energy is the rest energy plus the classical kinetic energy.
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer), §Special cases → Classical correspondence (expansion $E \approx mc^2 + \tfrac12 mv^2$ for $v \ll c$).

import Mathlib
import Definitions.Def_EnergyMomentum_basic

namespace EnergyMomentum

/-- Classical correspondence: `E = m c² + ½ m v² + o(v²)` as `v → 0`. -/
theorem classical_correspondence (m c : ℝ) (hc : 0 < c) (hm : 0 < m) :
    Filter.Tendsto
      (fun v : Vec3 => (energy m c v - m * c ^ 2 - m * ‖v‖ ^ 2 / 2) / ‖v‖ ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by sorry

end EnergyMomentum
