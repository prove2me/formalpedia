-- Prove2me | Theorems.Thm_BalancedAlgebra_leftCancellable_subalgebra
-- name    : BalancedAlgebra.leftCancellable_subalgebra
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:26:47.43351+00:00
-- url     : https://prove2.me/theorems/901f514f-2661-459c-89aa-d0c147a20eb9
-- title:
--   In an association the left cancellable elements form a subalgebra
-- statement:
--   Let $A$ be an **association** and call $b$ **left cancellable** when $b\cdot x=b\cdot y$, both defined, forces $x=y$.
--
--   $$a,b \text{ left cancellable},\ a\cdot b \text{ defined}\ \Longrightarrow\ a\cdot b \text{ left cancellable.}$$
--
--   Equivalently, the complement of the set of left cancellable elements — the elements the manuscript collects into the left ideal of non-left-cancellable elements — has a subalgebra as its complement, which is exactly the *primality* of that ideal. The argument is the displayed computation of §4: from $(ab)x=(ab)y$ one passes to $a(bx)=a(by)$ using the association, cancels $a$, and then cancels $b$.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §4 (p. 8): "Those elements which are not left cancellable form a left prime ideal. If a is left cancellable, and b is left cancellable, then (ab)x = (ab)y implies a(bx) = a(by) which implies that bx = by which implies x = y."

import Definitions.Def_BalancedAlgebra_core

namespace BalancedAlgebra

open PartialAlgebra

theorem leftCancellable_subalgebra {A : Type*} (P : PartialAlgebra A) (hP : P.IsAssociation) :
    P.IsSubalgebra {b : A | P.LeftCancellable b} := by sorry

end BalancedAlgebra
