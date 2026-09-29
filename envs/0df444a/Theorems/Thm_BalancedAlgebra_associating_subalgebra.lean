-- Prove2me | Theorems.Thm_BalancedAlgebra_associating_subalgebra
-- name    : BalancedAlgebra.associating_subalgebra
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:01:35.610545+00:00
-- url     : https://prove2.me/theorems/f6348679-bd3d-4b7c-94f7-2f3f67dea2c7
-- title:
--   The associating elements form a subalgebra
-- statement:
--   Call $b$ **associating** when, for all $a$ and $c$, the product $(ab)c$ is defined exactly when $a(bc)$ is, and the two agree whenever both are defined.
--
--   $$b,c \text{ associating and } b\cdot c \text{ defined}\ \Longrightarrow\ b\cdot c \text{ associating.}$$
--
--   That is, the associating elements of an arbitrary algebra are closed under the partial product, so they form a subalgebra — the one the manuscript calls the *associating subalgebra*, an algebra coinciding with it being an **association**. The verification is the bracket-chasing argument of §4, which uses each of the two hypotheses twice and requires no balance assumption.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §4 (p. 6): "The associating elements form a subalgebra ... The verification is straightforward. If b and c are associating, and bc is defined, then suppose that (a(bc))d is defined ..."

import Definitions.Def_BalancedAlgebra_core

namespace BalancedAlgebra

open PartialAlgebra

theorem associating_subalgebra {A : Type*} (P : PartialAlgebra A) :
    P.IsSubalgebra {b : A | P.Associating b} := by sorry

end BalancedAlgebra
