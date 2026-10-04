-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_isDenseOrder_iff_denselyOrdered
-- name    : AssumptionsOfPhysics.isDenseOrder_iff_denselyOrdered
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T11:51:20.115985+00:00
-- url     : https://prove2.me/theorems/6b5f8016-add9-41f2-847c-a62831d2f1f9
-- title:
--   Dense (infinite chains) iff an element between any two
-- statement:
--   A linearly ordered set is dense (between any two elements there is an infinite chain) if and only if between any two elements $a<b$ there is a third element $c$ with $a<c<b$.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 3 (pp. 169–195), Corollary 3.48, p. 189; Definition 3.47, p. 189

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

namespace AssumptionsOfPhysics
theorem isDenseOrder_iff_denselyOrdered (Q : Type*) [LinearOrder Q] :
    IsDenseOrder Q ↔ DenselyOrdered Q := by sorry
end AssumptionsOfPhysics
