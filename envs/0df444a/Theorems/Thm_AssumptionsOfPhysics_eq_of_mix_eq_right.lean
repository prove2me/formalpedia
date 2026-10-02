-- Prove2me | Theorems.Thm_AssumptionsOfPhysics_eq_of_mix_eq_right
-- name    : AssumptionsOfPhysics.eq_of_mix_eq_right
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T11:14:46.887805+00:00
-- url     : https://prove2.me/theorems/ba017ca6-6176-4faa-9d6d-7fd7a8ac01bf
-- title:
--   A non-trivial mixture equal to one of its ensembles
-- statement:
--   Let $a,b\in E$ with $pa+\bar pb=b$ for some $p\in(0,1]$. Then $a=b$.
-- source:
--   G. Carcassi, C. A. Aidala, Assumptions of Physics, Ver. 3.0 (Dec 31, 2025), https://assumptionsofphysics.org/book — Part II, Chapter 4 (pp. 197–284), Corollary 4.102, p. 241

import Mathlib
import Definitions.Def_AoP_EnsembleSpaces

namespace AssumptionsOfPhysics
theorem eq_of_mix_eq_right {I : ℝ → ℝ → ℝ} {E : Type*} [TopologicalSpace E]
    (X : EnsembleSpace I E) (a b : E) (p : unitInterval) (hp : 0 < (p : ℝ))
    (h : X.mix p a b = b) : a = b := by sorry
end AssumptionsOfPhysics
