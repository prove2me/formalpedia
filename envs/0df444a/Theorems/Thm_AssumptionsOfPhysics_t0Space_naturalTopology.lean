-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_t0Space_naturalTopology
-- name    : AssumptionsOfPhysics.t0Space_naturalTopology
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T16:01:51.901467+00:00
-- url     : https://prove2.me/theorems/b120bdcb-4a4a-4fae-b402-63a3db5382ee
-- title:
--   The natural topology is Kolmogorov (T0)
-- statement:
--   The natural topology on the possibilities of any experimental domain is Kolmogorov ($T_0$): any two distinct possibilities are separated by a verifiable set containing one but not the other.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 1 (pp. 101–146), Proposition 1.65, p. 138

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

namespace AssumptionsOfPhysics
theorem t0Space_naturalTopology {Ω : Type*} (D : ExperimentalDomain Ω) :
    T0Space D.Possibility := by sorry
end AssumptionsOfPhysics
