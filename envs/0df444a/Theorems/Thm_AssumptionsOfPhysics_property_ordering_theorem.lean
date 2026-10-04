-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_property_ordering_theorem
-- name    : AssumptionsOfPhysics.property_ordering_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T16:49:50.959643+00:00
-- url     : https://prove2.me/theorems/560fa988-77bf-4e5a-953f-dbe076404d15
-- title:
--   Property ordering theorem
-- statement:
--   **Goal (Property ordering theorem, Theorem 3.9).** An experimental domain $\mathcal D_X$ is fully characterized by a quantity $(Q,\le,q)$ if and only if it is naturally ordered and the possibilities are order isomorphic to the quantity.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 3 (pp. 169–195), Theorem 3.9, p. 173; Definitions 3.3, 3.6, 3.7, 3.8, pp. 171–173

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

namespace AssumptionsOfPhysics
theorem property_ordering_theorem {Ω : Type*} (D : ExperimentalDomain Ω) (Q : Type*)
    [LinearOrder Q] [TopologicalSpace Q] [OrderTopology Q] :
    D.IsFullyCharacterizedBy Q ↔
      ∃ r : LinearOrder D.Possibility, D.IsNaturalOrder r ∧
        Nonempty (@OrderIso D.Possibility Q r.toLE _) := by sorry
end AssumptionsOfPhysics
