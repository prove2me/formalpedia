-- Prove2me | Theorems.Thm_BalancedAlgebra_quiver_star_idem
-- name    : BalancedAlgebra.quiver_star_idem
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:00:11.361247+00:00
-- url     : https://prove2.me/theorems/ec982e34-0c32-4580-aae7-7eb6b603be46
-- title:
--   The two derived idempotence laws in a quiver
-- statement:
--   A **quiver**, in the equational form abstracted in §2, is a set of *arrows* equipped with two unary operations $a\mapsto{}^{*}a$ and $a\mapsto a^{*}$ subject to
--   $$ {}^{*}(a^{*})=a^{*}, \qquad ({}^{*}a)^{*}={}^{*}a. $$
--
--   Then for every arrow $a$,
--   $$ (a^{*})^{*}=a^{*}, \qquad {}^{*}({}^{*}a)={}^{*}a. $$
--
--   These are the two identities the manuscript calls a trivial consequence of the axioms, "though it may need a moment's thought to see why". They say that the images of the two operations consist of the *units* (vertices) of the quiver: an arrow lies in the image of one operation exactly when it is fixed by both.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §2 (p. 5): "It is then a trivial consequence of these two axioms that (a*)* = a*, and likewise *(*a) = *a."

import Definitions.Def_BalancedAlgebra_core

namespace BalancedAlgebra

open PartialAlgebra

theorem quiver_star_idem {A : Type*} (dom cod : A → A)
    (h1 : ∀ a : A, dom (cod a) = cod a) (h2 : ∀ a : A, cod (dom a) = dom a) (a : A) :
    cod (cod a) = cod a ∧ dom (dom a) = dom a := by sorry

end BalancedAlgebra
