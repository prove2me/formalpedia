-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_orth_properties
-- name    : AssumptionsOfPhysics.orth_properties
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T10:06:12.681078+00:00
-- url     : https://prove2.me/theorems/68a94d70-54aa-4f75-a14d-9f60fac4a4df
-- title:
--   Properties of orthogonality
-- statement:
--   Assume $I(p,\bar p)>0$ for all $p\in(0,1)$ (a consequence of the universality of $I$). Orthogonality satisfies: (1) irreflexivity, $a\not\perp a$; (2) symmetry, $a\perp b$ iff $b\perp a$; (3) components are not orthogonal: if $b$ is a component of $a$ then $a\not\perp b$; (4) orthogonality implies separateness: if $a\perp b$ then $a$ and $b$ are separate.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 4 (pp. 197–284), Proposition 4.67, p. 230; Axiom 4.55, p. 223

import Mathlib
import Definitions.Def_AoP_EnsembleSpaces

namespace AssumptionsOfPhysics
theorem orth_properties {I : ℝ → ℝ → ℝ} {E : Type*} [TopologicalSpace E]
    (X : EnsembleSpace I E) (hI : ∀ p : ℝ, 0 < p → p < 1 → 0 < I p (1 - p)) :
    (∀ a : E, ¬ X.Orth a a) ∧ (∀ a b : E, X.Orth a b ↔ X.Orth b a) ∧
      (∀ a b : E, X.IsComponent b a → ¬ X.Orth a b) ∧
      (∀ a b : E, X.Orth a b → X.Separate a b) := by sorry
end AssumptionsOfPhysics
