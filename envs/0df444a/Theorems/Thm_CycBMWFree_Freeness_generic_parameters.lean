-- Prove2me | Theorems.Thm_CycBMWFree_Freeness_generic_parameters
-- name    : CycBMWFree.Freeness.generic_parameters
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:57.615467+00:00
-- url     : https://prove2.me/theorems/371680b9-76f1-4e81-9ed0-be66f610a71f
-- title:
--   §3.4, pp. 28–29 — existence and u-admissibility of the generic parameters
-- statement:
--   For $r\ge1$, let $F=\mathbb Q(q,u_1,\ldots,u_r)$, let $p=\prod_j u_j$, set $ρ=p$ when $r$ is odd and $ρ=q^{-1}p$ when $r$ is even, and set $δ_a=\sum_jγ_j u_j^a$ with $γ_j$ from (3.6). There is a ground-parameter structure on $F$ with exactly these values, and every ground-parameter structure with these values is $u$-admissible:
--   $$
--   \exists P,\ \operatorname{Generic}(P),\qquad \forall P,\ \operatorname{Generic}(P)\Longrightarrow \operatorname{UAdmissible}(P).
--   $$
--   This supplies an inhabited generic instance for the later dimension and semisimplicity statements. **Formalization Note** The paper constructs the localization $S_0[δ_0^{-1}]$; this milestone states its fraction-field consequence.
-- source:
--   Goodman & Hauschild Mosley, Cyclotomic BMW algebras II, arXiv:math/0612065v5, pp. 28–29, §3.4

import Mathlib
import Definitions.Def_CycBMWFree_Freeness_Setting

noncomputable section
open scoped BigOperators

namespace CycBMWFree.Freeness
open QAlgorithms.Papers.Independent.Support21.P14

/-- The §3.4 generic parameters exist and are u-admissible, pp. 28–29. -/
theorem generic_parameters (r : ℕ) (hr : 0 < r) :
    (∃ P : GroundParameters (GenericField r) r, IsGenericParameters P) ∧
    ∀ P : GroundParameters (GenericField r) r, IsGenericParameters P → UAdmissible P := by sorry

end CycBMWFree.Freeness
