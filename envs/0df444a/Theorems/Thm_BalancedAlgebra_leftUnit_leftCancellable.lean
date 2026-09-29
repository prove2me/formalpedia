-- Prove2me | Theorems.Thm_BalancedAlgebra_leftUnit_leftCancellable
-- name    : BalancedAlgebra.leftUnit_leftCancellable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:26:03.363994+00:00
-- url     : https://prove2.me/theorems/8aa13133-2cd4-4713-aabe-e3db3f27ff94
-- title:
--   Left units are left cancellable
-- statement:
--   Call $b$ **left cancellable** when $b\cdot x=b\cdot y$, with both products defined, forces $x=y$.
--
--   $$u \text{ a left unit}\ \Longrightarrow\ u \text{ is left cancellable.}$$
--
--   The manuscript records this while showing that the non-left-cancellable elements form a prime left ideal: since left units are left cancellable, an algebra all of whose elements fail to be left cancellable can have no left units at all.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §4 (p. 8): "Notice that the left units are all left cancellable: ux = uy implies x = y."

import Definitions.Def_BalancedAlgebra_core

namespace BalancedAlgebra

open PartialAlgebra

theorem leftUnit_leftCancellable {A : Type*} (P : PartialAlgebra A) (u : A) (hu : P.IsLeftUnit u) :
    P.LeftCancellable u := by sorry

end BalancedAlgebra
