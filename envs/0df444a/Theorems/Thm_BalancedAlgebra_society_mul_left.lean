-- Prove2me | Theorems.Thm_BalancedAlgebra_society_mul_left
-- name    : BalancedAlgebra.society_mul_left
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:23:58.608526+00:00
-- url     : https://prove2.me/theorems/e8371883-715d-4623-bc98-c0672912a32c
-- title:
--   The society is closed under multiplication on the left
-- statement:
--   With **gregarious** and **associating** as before:
--
--   $$a \text{ associating},\ b \text{ gregarious and associating},\ a\cdot b=e\ \Longrightarrow\ e \text{ gregarious and associating.}$$
--
--   This is the left-handed companion of the previous milestone — the manuscript's "The proof on the other side is similar" — and the two together are the statement that the gregarious associating elements form a two-sided ideal in the associating subalgebra. Since the ambient definitions are self-dual under reversing the product, a contributor may either repeat the argument with the roles of the outer factors exchanged or formalize the opposite algebra once and transport the right-handed result.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §4.2 (p. 7): "The proof on the other side is similar. So the gregarious, associating elements of an algebra form an ideal in the subalgebra of associating elements, called its society."

import Definitions.Def_BalancedAlgebra_core

namespace BalancedAlgebra

open PartialAlgebra

theorem society_mul_left {A : Type*} (P : PartialAlgebra A) (a b e : A)
    (ha : P.Associating a) (hbg : P.Gregarious b) (hb : P.Associating b)
    (hab : P.op a b = some e) : P.Gregarious e ∧ P.Associating e := by sorry

end BalancedAlgebra
