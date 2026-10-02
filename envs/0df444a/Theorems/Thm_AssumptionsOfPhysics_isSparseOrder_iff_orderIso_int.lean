-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_isSparseOrder_iff_orderIso_int
-- name    : AssumptionsOfPhysics.isSparseOrder_iff_orderIso_int
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T11:15:14.038254+00:00
-- url     : https://prove2.me/theorems/2270294e-feb7-4eb0-a68c-6588545f5d97
-- title:
--   Sparse linear orders are the contiguous subsets of the integers
-- statement:
--   A linear order is sparse if and only if it is order isomorphic to a contiguous subset of the integers.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 3 (pp. 169–195), Proposition 3.42, p. 186; Definitions 3.39, 3.40, p. 186

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

namespace AssumptionsOfPhysics
theorem isSparseOrder_iff_orderIso_int (Q : Type*) [LinearOrder Q] :
    IsSparseOrder Q ↔ ∃ S : Set ℤ, S.OrdConnected ∧ Nonempty (Q ≃o S) := by sorry
end AssumptionsOfPhysics
