-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_isDecidable_iff_discrete_quantity
-- name    : AssumptionsOfPhysics.isDecidable_iff_discrete_quantity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T14:25:12.733518+00:00
-- url     : https://prove2.me/theorems/029c35fa-f315-44cd-b59b-38811d44af9d
-- title:
--   Decidable domains are those characterized by a discrete quantity
-- statement:
--   An experimental domain is decidable if and only if it is fully characterized by a discrete quantity.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 3 (pp. 169–195), Proposition 3.46, p. 188

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

namespace AssumptionsOfPhysics
theorem isDecidable_iff_discrete_quantity {Ω : Type*} (D : ExperimentalDomain Ω) :
    D.IsDecidable ↔
      ∃ (Q : Type) (_ : LinearOrder Q) (_ : TopologicalSpace Q) (_ : OrderTopology Q),
        IsSparseOrder Q ∧ D.IsFullyCharacterizedBy Q := by sorry
end AssumptionsOfPhysics
