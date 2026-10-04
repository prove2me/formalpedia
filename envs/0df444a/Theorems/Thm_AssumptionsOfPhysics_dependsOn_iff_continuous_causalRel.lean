-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_dependsOn_iff_continuous_causalRel
-- name    : AssumptionsOfPhysics.dependsOn_iff_continuous_causalRel
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T14:25:36.300007+00:00
-- url     : https://prove2.me/theorems/708aecd5-2fed-4037-b38c-90e6008575af
-- title:
--   Experimental relationship theorem (inference ⇔ continuous causal relationship)
-- statement:
--   **Goal (Experimental Relationship Theorem, Theorem 2.10, with continuity made explicit).** Let $\mathcal D_X,\mathcal D_Y$ be experimental domains. An inference relationship $r:\mathcal D_Y\to\mathcal D_X$ exists if and only if there is a causal relationship $f:X\to Y$ that is continuous for the natural topologies. *Deviation from the source:* the book states the equivalence for causal relationships without explicitly requiring continuity, and asserts (Corollary 2.8) that every causal relationship is continuous. That fails for $\Omega=\{0,1\}$, $\mathcal D_X=\{\emptyset,\{1\},\Omega\}$, $\mathcal D_Y=\{\emptyset,\{0\},\Omega\}$, where the identity on possibilities is causal but not continuous and $\mathcal D_Y$ does not depend on $\mathcal D_X$. The continuity requirement is the one used in the book's proof.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 2 (pp. 149–168), Theorem 2.10, p. 153 (with Definition 2.7 and Corollary 2.8)

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_DomainRelationships

namespace AssumptionsOfPhysics
theorem dependsOn_iff_continuous_causalRel {Ω : Type*} (DX DY : ExperimentalDomain Ω) :
    ExperimentalDomain.DependsOn DY DX ↔
      ∃ f : DX.Possibility → DY.Possibility,
        ExperimentalDomain.IsCausalRel DX DY f ∧ Continuous f := by sorry
end AssumptionsOfPhysics
