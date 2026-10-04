-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_discreteTopology_iff_isDecidable
-- name    : AssumptionsOfPhysics.discreteTopology_iff_isDecidable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T18:12:19.914973+00:00
-- url     : https://prove2.me/theorems/e25a4188-a247-477c-b80c-ba244b0b5a02
-- title:
--   Decidability is discreteness
-- statement:
--   The natural topology of the possibilities $X$ of an experimental domain $\mathcal D$ is discrete if and only if $\mathcal D$ is decidable.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 1 (pp. 101–146), Theorem 1.76, p. 142; Definition 1.73, p. 141; Definition 1.75, p. 142

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

namespace AssumptionsOfPhysics
theorem discreteTopology_iff_isDecidable {Ω : Type*} (D : ExperimentalDomain Ω) :
    DiscreteTopology D.Possibility ↔ D.IsDecidable := by sorry
end AssumptionsOfPhysics
