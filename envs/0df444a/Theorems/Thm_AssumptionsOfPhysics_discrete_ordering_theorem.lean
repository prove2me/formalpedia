-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_discrete_ordering_theorem
-- name    : AssumptionsOfPhysics.discrete_ordering_theorem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T13:46:30.661988+00:00
-- url     : https://prove2.me/theorems/a7d262ba-8fd5-442b-8162-4b7cee193c9f
-- title:
--   Discrete ordering theorem (natural sparse order ⇔ discrete quantity)
-- statement:
--   For an experimental domain $\mathcal D_X$ the following are equivalent: (1) the domain has a natural sparse order; (2) the domain is fully characterized by a discrete quantity, i.e. a quantity $(Q,\le,q)$ whose order is sparse.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 3 (pp. 169–195), Theorem 3.44 (equivalence of items 1 and 2), p. 187; Definition 3.43, p. 187

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

namespace AssumptionsOfPhysics
theorem discrete_ordering_theorem {Ω : Type*} (D : ExperimentalDomain Ω) :
    (∃ r : LinearOrder D.Possibility, D.IsNaturalOrder r ∧ @IsSparseOrder _ r.toPreorder) ↔
      ∃ (Q : Type) (_ : LinearOrder Q) (_ : TopologicalSpace Q) (_ : OrderTopology Q),
        IsSparseOrder Q ∧ D.IsFullyCharacterizedBy Q := by sorry
end AssumptionsOfPhysics
