-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_finite_possibilities_tfae
-- name    : AssumptionsOfPhysics.finite_possibilities_tfae
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T13:46:57.889741+00:00
-- url     : https://prove2.me/theorems/8135f9cf-28e2-4f3a-b71b-7a52dede5f36
-- title:
--   Finitely many possibilities iff finitely many statements iff a finite basis
-- statement:
--   For an experimental domain $\mathcal D$ with possibilities $X$ the following are equivalent: (1) $X$ is finite; (2) $\mathcal D$ contains finitely many verifiable statements; (3) $\mathcal D$ has a finite basis.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 1 (pp. 101–146), Proposition 1.53, pp. 132–133

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

namespace AssumptionsOfPhysics
theorem finite_possibilities_tfae {Ω : Type*} (D : ExperimentalDomain Ω) :
    List.TFAE [Finite D.Possibility, D.stmts.Finite,
      ∃ B : Set (Set Ω), B.Finite ∧ IsBasis D.stmts B] := by sorry
end AssumptionsOfPhysics
