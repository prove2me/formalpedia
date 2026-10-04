-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_continuous_ordering_theorem
-- name    : AssumptionsOfPhysics.continuous_ordering_theorem
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T14:46:34.17279+00:00
-- url     : https://prove2.me/theorems/4af7c390-8555-4b90-bcf4-ed5fddcb32b9
-- title:
--   Continuous ordering theorem (natural dense complete separable order ⇔ continuous quantity)
-- statement:
--   For an experimental domain $\mathcal D_X$ the following are equivalent: (1) the domain has a natural dense complete order that has a countable dense subset; (2) the domain is fully characterized by a continuous quantity $(U,\le,q)$, $U\subseteq\mathbb R$ contiguous with its order topology.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 3 (pp. 169–195), Theorem 3.53 (equivalence of items 1 and 2), p. 190; Definition 3.52, p. 190

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

namespace AssumptionsOfPhysics
theorem continuous_ordering_theorem {Ω : Type*} (D : ExperimentalDomain Ω) :
    (∃ r : LinearOrder D.Possibility, D.IsNaturalOrder r ∧ @IsDenseOrder _ r.toPreorder ∧
        @IsCompleteOrder _ r.toPreorder ∧
        ∃ A : Set D.Possibility, A.Countable ∧ @IsDenseSubset _ r.toPreorder A) ↔
      ∃ U : Set ℝ, U.OrdConnected ∧
        Nonempty (@Homeomorph D.Possibility U _ (Preorder.topology U)) := by sorry
end AssumptionsOfPhysics
