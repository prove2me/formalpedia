-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_isOpen_iff_verifiableSet
-- name    : AssumptionsOfPhysics.isOpen_iff_verifiableSet
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T14:46:41.644331+00:00
-- url     : https://prove2.me/theorems/4594b8dd-5685-4359-9ca2-ae8ddeaf9162
-- title:
--   The open sets of the natural topology are exactly the verifiable sets
-- statement:
--   The verifiable sets $U(s)$, $s\in\mathcal D$, are already closed under arbitrary unions and finite intersections and contain $\emptyset$ and $X$: a set of possibilities is open in the natural topology if and only if it equals $U(s)$ for some verifiable statement $s\in\mathcal D$. Thus $\mathcal T_X=U(\mathcal D)$.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 1 (pp. 101–146), Proposition 1.57, p. 135

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

namespace AssumptionsOfPhysics
theorem isOpen_iff_verifiableSet {Ω : Type*} (D : ExperimentalDomain Ω)
    (U : Set D.Possibility) : IsOpen U ↔ ∃ s ∈ D.stmts, D.verifiableSet s = U := by sorry
end AssumptionsOfPhysics
