-- Prove2me | Theorems.Thm_CycBMWFree_Freeness_theorem_5_2
-- name    : CycBMWFree.Freeness.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:28:01.337707+00:00
-- url     : https://prove2.me/theorems/03aaebf0-cde1-4789-bdf9-042f32058cf4
-- title:
--   Theorem 5.2, p. 44 — generic BMW dimension
-- statement:
--   Let $F=\mathbb Q(q,u_1,\ldots,u_r)$ carry the generic ground parameters of §3.4. For every $n$, the cyclotomic BMW algebra is finite dimensional and
--   $$
--   \dim_F W_{n,F,r}=r^n(2n-1)!!.
--   $$
--   The dimension matches the size of the spanning family and is the generic lower bound needed for freeness. **Formalization Note** The generic parameter predicate is inhabited by the §3.4 milestone; the statement is not extended to arbitrary, possibly nonadmissible field parameters.
-- source:
--   Goodman & Hauschild Mosley, Cyclotomic BMW algebras II, arXiv:math/0612065v5, p. 44, Theorem 5.2

import Mathlib
import Definitions.Def_CycBMWFree_Freeness_Setting

noncomputable section
open scoped BigOperators

namespace CycBMWFree.Freeness
open QAlgorithms.Papers.Independent.Support21.P14

/-- The generic dimension, Theorem 5.2, p. 44. -/
theorem theorem_5_2 (r : ℕ) (P : GroundParameters (GenericField r) r)
    (hP : IsGenericParameters P) (n : ℕ) :
    Module.Finite (GenericField r) (BMW P n) ∧
      Module.finrank (GenericField r) (BMW P n) = rankN r n := by sorry

end CycBMWFree.Freeness
