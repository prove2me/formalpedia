-- Prove2me | Theorems.Thm_EnergyMomentum_rest_frame
-- name    : EnergyMomentum.rest_frame
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:13:31.805207+00:00
-- url     : https://prove2.me/theorems/18365132-76d4-4f04-8e8a-e38b0cbc62bb
-- title:
--   Rest frame: $\mathbf p = 0$ and $E = E_0 = mc^2$
-- statement:
--   For a body of mass $m$ at rest ($\mathbf v = 0$) and any value of the constant $c$, the relativistic momentum vanishes and the total energy equals the rest energy:
--
--   $$
--   \mathbf p = 0, \qquad E = E_0 = mc^2 .
--   $$
--
--   This is the centre-of-momentum frame of a single particle, in which (1) reduces to mass–energy equivalence.
-- source:
--   Wikipedia, *Energy–momentum relation*, https://en.wikipedia.org/wiki/Energy%E2%80%93momentum_relation (PDF snapshot supplied by the proposer), §Special cases → Centre-of-momentum frame (one particle).

import Mathlib
import Definitions.Def_EnergyMomentum_basic

namespace EnergyMomentum

/-- Centre-of-momentum frame of one particle: at rest, `p = 0` and `E = E₀ = m c²`. -/
theorem rest_frame (m c : ℝ) :
    momentum m c 0 = 0 ∧ energy m c 0 = restEnergy m c ∧ restEnergy m c = m * c ^ 2 := by sorry

end EnergyMomentum
