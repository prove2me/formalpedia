-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_decidable_tfae
-- name    : AssumptionsOfPhysics.decidable_tfae
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T17:14:51.15685+00:00
-- url     : https://prove2.me/theorems/1f5c3797-73ce-48a7-9b1a-bb1576a7276c
-- title:
--   Characterizations of decidable experimental domains
-- statement:
--   For an experimental domain $\mathcal D$ the following are equivalent: (1) $\mathcal D$ is decidable; (2) $\mathcal D$ coincides with its theoretical domain $\bar{\mathcal D}$; (3) all possibilities are verifiable; (4) the possibilities form a countable basis of $\mathcal D$.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 1 (pp. 101–146), Proposition 1.74, pp. 141–142; Definition 1.73, p. 141

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

namespace AssumptionsOfPhysics
theorem decidable_tfae {Ω : Type*} (D : ExperimentalDomain Ω) :
    List.TFAE [D.IsDecidable, D.theoretical = D.stmts,
      ∀ x : D.Possibility, x.val ∈ D.stmts,
      D.possibilities.Countable ∧ IsBasis D.stmts D.possibilities] := by sorry
end AssumptionsOfPhysics
