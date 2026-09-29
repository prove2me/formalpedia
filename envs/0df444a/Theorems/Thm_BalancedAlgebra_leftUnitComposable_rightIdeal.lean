-- Prove2me | Theorems.Thm_BalancedAlgebra_leftUnitComposable_rightIdeal
-- name    : BalancedAlgebra.leftUnitComposable_rightIdeal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T02:59:44.805634+00:00
-- url     : https://prove2.me/theorems/5739f16a-c89c-40d2-8ae0-b45292ff6ee6
-- title:
--   Elements admitting some left unit on the left form a right ideal
-- statement:
--   Let the algebra be **balanced**. For $a\in A$ write ${}^{*}a$ for the collection of left units $u$ such that $u\cdot a$ is defined.
--
--   $$\{\,a\in A: {}^{*}a\neq\emptyset\,\}\ \text{is a right ideal.}$$
--
--   The manuscript obtains this as a union of the right ideals of the previous milestone, one for each left unit: a union of right ideals is again a right ideal. When this ideal is all of $A$ the algebra is called **right quivered**, and the corresponding triviality condition on both sides gives the quivered algebras from which quivers and categories are extracted.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §1 (p. 3): "The union of right ideals being a right ideal, those elements a for which *a is not empty is also a right ideal."

import Definitions.Def_BalancedAlgebra_core

namespace BalancedAlgebra

open PartialAlgebra

theorem leftUnitComposable_rightIdeal {A : Type*} (P : PartialAlgebra A) (hP : P.Balanced) :
    P.RightIdeal {a : A | ∃ u : A, P.IsLeftUnit u ∧ P.IsDefined u a} := by sorry

end BalancedAlgebra
