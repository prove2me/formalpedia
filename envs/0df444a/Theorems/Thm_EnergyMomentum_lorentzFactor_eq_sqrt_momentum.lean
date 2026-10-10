-- Prove2me | Theorems.Thm_EnergyMomentum_lorentzFactor_eq_sqrt_momentum
-- name    : EnergyMomentum.lorentzFactor_eq_sqrt_momentum
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:11:16.846501+00:00
-- url     : https://prove2.me/theorems/fa7b1cc7-11f5-43bf-98de-9cdf367407d2
-- title:
--   Lorentz factor in terms of momentum: $\gamma = \sqrt{1 + (p/mc)^2}$
-- statement:
--   Let $c > 0$, $m > 0$ and let $\mathbf v \in \mathbb R^3$ with $|\mathbf v| < c$. With $\gamma = 1/\sqrt{1-(|\mathbf v|/c)^2}$ and relativistic momentum $\mathbf p = \gamma m\mathbf v$, $p = |\mathbf p|$,
--
--   $$
--   \gamma = \sqrt{1 + \left(\frac{p}{mc}\right)^2}.
--   $$
--
--   This alternative form expresses the Lorentz factor through momentum and mass instead of velocity.
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer), §Origins and derivation of the equation → Heuristic approach for massive particles (alternative form of the Lorentz factor).

import Mathlib
import Definitions.Def_EnergyMomentum_basic

namespace EnergyMomentum

/-- Lorentz factor in terms of three-momentum: `γ = √(1 + (p / (m c))²)`. -/
theorem lorentzFactor_eq_sqrt_momentum (m c : ℝ) (v : Vec3)
    (hc : 0 < c) (hm : 0 < m) (hv : ‖v‖ < c) :
    lorentzFactor c v = Real.sqrt (1 + (‖momentum m c v‖ / (m * c)) ^ 2) := by sorry

end EnergyMomentum
