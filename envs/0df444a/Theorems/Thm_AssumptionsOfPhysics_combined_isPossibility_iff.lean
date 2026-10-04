-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_combined_isPossibility_iff
-- name    : AssumptionsOfPhysics.combined_isPossibility_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T13:46:04.930418+00:00
-- url     : https://prove2.me/theorems/95354e79-3e1a-4ccc-9ed3-8005cbed93d6
-- title:
--   Possibilities of a combined domain
-- statement:
--   Let $\{\mathcal D_{X_i}\}_{i\in\iota}$ be a countable family of experimental domains and $\mathcal D_X$ their combined domain. A statement $x$ is a possibility of $\mathcal D_X$ if and only if $x$ is not impossible and $x=\bigwedge_i x_i$ for some choice of possibilities $x_i\in X_i$.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 2 (pp. 149–168), Proposition 2.14, p. 157; Definition 2.13, p. 156

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_DomainRelationships

namespace AssumptionsOfPhysics
theorem combined_isPossibility_iff {Ω : Type*} {ι : Type*} [Countable ι]
    (Dfam : ι → ExperimentalDomain Ω) (x : Set Ω) :
    (ExperimentalDomain.combined Dfam).IsPossibility x ↔
      x.Nonempty ∧ ∃ xs : ι → Set Ω, (∀ i, (Dfam i).IsPossibility (xs i)) ∧ x = ⋂ i, xs i := by sorry
end AssumptionsOfPhysics
