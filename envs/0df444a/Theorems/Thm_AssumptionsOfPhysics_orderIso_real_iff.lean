-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_orderIso_real_iff
-- name    : AssumptionsOfPhysics.orderIso_real_iff
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T13:25:51.850984+00:00
-- url     : https://prove2.me/theorems/c9071ca0-270a-4955-a3ff-6ce11d82264c
-- title:
--   Characterization of the contiguous subsets of the reals
-- statement:
--   A linearly ordered set is dense, complete and has a countable dense subset if and only if it is order isomorphic to a contiguous subset of the real numbers.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 3 (pp. 169–195), Theorem 3.51, p. 189; Definitions 3.47, 3.49, 3.50, p. 189

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

namespace AssumptionsOfPhysics
theorem orderIso_real_iff (Q : Type*) [LinearOrder Q] :
    (IsDenseOrder Q ∧ IsCompleteOrder Q ∧ ∃ A : Set Q, A.Countable ∧ IsDenseSubset A) ↔
      ∃ S : Set ℝ, S.OrdConnected ∧ Nonempty (Q ≃o S) := by sorry
end AssumptionsOfPhysics
