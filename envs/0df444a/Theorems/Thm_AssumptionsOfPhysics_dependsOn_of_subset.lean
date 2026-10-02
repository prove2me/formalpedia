-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_dependsOn_of_subset
-- name    : AssumptionsOfPhysics.dependsOn_of_subset
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T10:05:14.364767+00:00
-- url     : https://prove2.me/theorems/d9a8f165-7996-4aed-bc97-521e58a4f9ce
-- title:
--   Sub-domains are dependent domains
-- statement:
--   If the statements of an experimental domain $\mathcal D_Y$ are a subset of those of an experimental domain $\mathcal D_X$, then $\mathcal D_Y$ depends on $\mathcal D_X$.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 2 (pp. 149–168), Corollary 2.3, p. 150

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_DomainRelationships

namespace AssumptionsOfPhysics
theorem dependsOn_of_subset {Ω : Type*} (DX DY : ExperimentalDomain Ω)
    (h : DY.stmts ⊆ DX.stmts) : ExperimentalDomain.DependsOn DY DX := by sorry
end AssumptionsOfPhysics
