-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_naturalTopology_main
-- name    : AssumptionsOfPhysics.naturalTopology_main
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T19:34:29.814308+00:00
-- url     : https://prove2.me/theorems/1092a25d-771d-42f6-bb5d-b61881e6a18c
-- title:
--   Natural topology of an experimental domain: exactly the verifiable sets, second-countable and T0
-- statement:
--   **Goal.** Let $\mathcal D$ be an experimental domain with possibilities $X$. The verifiable sets $U(s)$, $s\in\mathcal D$, are exactly the open sets of a topology on $X$ (the natural topology, Proposition 1.57); this topology is second-countable (Proposition 1.61) and Kolmogorov $T_0$ (Proposition 1.65). In short, the possibilities of an experimental domain form a second-countable $T_0$ space whose open sets are precisely the verifiable statements.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 1 (pp. 101–146), Propositions 1.57, 1.61 and 1.65, pp. 135–138

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains

namespace AssumptionsOfPhysics
theorem naturalTopology_main {Ω : Type*} (D : ExperimentalDomain Ω) :
    (∀ U : Set D.Possibility, IsOpen U ↔ ∃ s ∈ D.stmts, D.verifiableSet s = U) ∧
      SecondCountableTopology D.Possibility ∧ T0Space D.Possibility := by sorry
end AssumptionsOfPhysics
