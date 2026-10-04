-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_mixingEntropy_properties
-- name    : AssumptionsOfPhysics.mixingEntropy_properties
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-02T11:51:04.321517+00:00
-- url     : https://prove2.me/theorems/82aa2aef-e4d8-46f8-a19e-17117ea6d11b
-- title:
--   Properties of the mixing entropy
-- statement:
--   The mixing entropy satisfies: (1) $MS(a,b)\ge0$; (2) $MS(a,b)=0$ iff $a=b$; (3) $MS(a,b)\le I(\tfrac12,\tfrac12)$; (5) $MS(a,b)=MS(b,a)$. *(The book states (3) as $MS\le 1$ using the normalization $I(\tfrac12,\tfrac12)=1$ of Theorem 4.59, and also lists (4) $MS=1\iff a\perp b$; (4) is not included here.)*
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 4 (pp. 197–284), Proposition 4.116, p. 245; Definition 4.115, p. 245

import Mathlib
import Definitions.Def_AoP_EnsembleSpaces

namespace AssumptionsOfPhysics
theorem mixingEntropy_properties {I : ℝ → ℝ → ℝ} {E : Type*} [TopologicalSpace E]
    (X : EnsembleSpace I E) :
    (∀ a b : E, 0 ≤ X.mixingEntropy a b) ∧ (∀ a b : E, X.mixingEntropy a b = 0 ↔ a = b) ∧
      (∀ a b : E, X.mixingEntropy a b ≤ I (1 / 2) (1 / 2)) ∧
      (∀ a b : E, X.mixingEntropy a b = X.mixingEntropy b a) := by sorry
end AssumptionsOfPhysics
