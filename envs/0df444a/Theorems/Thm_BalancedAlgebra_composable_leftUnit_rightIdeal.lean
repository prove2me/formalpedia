-- Prove2me | Theorems.Thm_BalancedAlgebra_composable_leftUnit_rightIdeal
-- name    : BalancedAlgebra.composable_leftUnit_rightIdeal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T01:38:03.104023+00:00
-- url     : https://prove2.me/theorems/bcc882fb-9d7b-446b-a761-475c01e5976a
-- title:
--   Elements composable with a fixed left unit form a right ideal
-- statement:
--   Let the algebra be **balanced**: for all $a,b,c$, the product $(a\cdot b)\cdot c$ is defined exactly when $a\cdot(b\cdot c)$ is. Let $u$ be a left unit.
--
--   $$\{\,b\in A: u\cdot b \text{ is defined}\,\}\ \text{is a right ideal.}$$
--
--   In the manuscript this is the specialization of the first component of the balance axiom to a left unit: if $u\cdot b$ is defined and $b\cdot c$ is defined, then $u\cdot(b\cdot c)$ is defined, so the set of elements composable with $u$ on the left is closed under multiplication on the right. Taking the union over all left units yields the ideal used to define quivered algebras.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §1 (p. 3): "Consider now a left unit u. Then the first axiom specializes to the statement that if ub is defined and bc is defined, then u(bc) is defined. Thus those elements composable with u on the left form a right ideal."

import Definitions.Def_BalancedAlgebra_core

namespace BalancedAlgebra

open PartialAlgebra

theorem composable_leftUnit_rightIdeal {A : Type*} (P : PartialAlgebra A) (hP : P.Balanced)
    (u : A) (hu : P.IsLeftUnit u) : P.RightIdeal {b : A | P.IsDefined u b} := by sorry

end BalancedAlgebra
