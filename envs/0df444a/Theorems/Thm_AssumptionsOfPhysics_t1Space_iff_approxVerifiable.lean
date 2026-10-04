-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_t1Space_iff_approxVerifiable
-- name    : AssumptionsOfPhysics.t1Space_iff_approxVerifiable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T16:49:55.829239+00:00
-- url     : https://prove2.me/theorems/711cfcf2-3ccd-432e-8bbb-2e6112b10da0
-- title:
--   The natural topology is T1 iff all possibilities are approximately verifiable
-- statement:
--   The natural topology on the possibilities of an experimental domain is Fréchet ($T_1$) if and only if every possibility is approximately verifiable, i.e. is the countable conjunction of verifiable statements of the domain.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 1 (pp. 101–146), Proposition 1.66, p. 138; Definition 1.38, p. 126

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

namespace AssumptionsOfPhysics
theorem t1Space_iff_approxVerifiable {Ω : Type*} (D : ExperimentalDomain Ω) :
    T1Space D.Possibility ↔ ∀ x : D.Possibility, D.IsApproxVerifiable x.val := by sorry
end AssumptionsOfPhysics
