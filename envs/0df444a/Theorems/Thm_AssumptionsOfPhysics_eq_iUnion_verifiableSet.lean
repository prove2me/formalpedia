-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_eq_iUnion_verifiableSet
-- name    : AssumptionsOfPhysics.eq_iUnion_verifiableSet
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T14:25:27.243261+00:00
-- url     : https://prove2.me/theorems/ae4a0fc5-dadd-46ed-9d45-f7cd99fa6002
-- title:
--   A verifiable statement is the disjunction of its verifiable set
-- statement:
--   Every verifiable statement $s\in\mathcal D$ is equivalent to the disjunction of the possibilities in its verifiable set: $s\equiv\bigvee_{x\in U(s)} x$.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 1 (pp. 101–146), Proposition 1.56, p. 135

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

namespace AssumptionsOfPhysics
theorem eq_iUnion_verifiableSet {Ω : Type*} (D : ExperimentalDomain Ω) (s : Set Ω)
    (hs : s ∈ D.stmts) : s = ⋃ x ∈ D.verifiableSet s, x.val := by sorry
end AssumptionsOfPhysics
