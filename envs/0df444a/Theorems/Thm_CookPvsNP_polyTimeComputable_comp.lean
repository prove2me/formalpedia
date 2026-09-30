-- Prove2me | Theorems.Thm_CookPvsNP_polyTimeComputable_comp
-- name    : CookPvsNP.polyTimeComputable_comp
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T06:26:41.254192+00:00
-- url     : https://prove2.me/theorems/028ccdb8-1f42-4651-94d3-63758b6500fd
-- title:
--   Cook, Definition 3 — polynomial-time computable functions are closed under composition
-- statement:
--   Cook's polynomial-time many-one reducibility (Definition 3, p. 2) compares languages by means of polynomial-time computable functions. This is the closure of that function class under composition: if f is polynomial-time computable from Σ₁* to Σ₂* and g is polynomial-time computable from Σ₂* to Σ₃*, then g after f is polynomial-time computable as well. It is exactly what makes reducibility itself transitive, and hence what allows an NP-hardness argument to be assembled as a chain of separate reductions instead of one monolithic function. The proof is the standard simulation of the first machine followed by the second, on one tape, with the polynomial time bounds composed.
-- source:
--   Cook, The P versus NP problem, Clay Mathematics Institute (2000), §1 p. 2 and Definition 3 p. 2

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace CookPvsNP

/-- Polynomial-time computable functions are closed under composition. -/
theorem polyTimeComputable_comp {Sym₁ Sym₂ Sym₃ : Type}
    (f : List Sym₁ → List Sym₂) (g : List Sym₂ → List Sym₃)
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (g ∘ f) := by
  sorry

end CookPvsNP
