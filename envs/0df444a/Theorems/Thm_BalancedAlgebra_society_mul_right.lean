-- Prove2me | Theorems.Thm_BalancedAlgebra_society_mul_right
-- name    : BalancedAlgebra.society_mul_right
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:16:32.442889+00:00
-- url     : https://prove2.me/theorems/53cf7d78-6988-4706-b0e9-831ded60718c
-- title:
--   The society is closed under multiplication on the right
-- statement:
--   Call an element **gregarious** if, whenever $a\cdot b$ and $b\cdot c$ are defined, at least one bracketing of $abc$ is defined, and **associating** if the two bracketings are defined together and then agree.
--
--   $$b \text{ gregarious and associating},\ c \text{ associating},\ b\cdot c=e\ \Longrightarrow\ e \text{ gregarious and associating.}$$
--
--   This is the computation of §4.2, which shows that the gregarious associating elements of an arbitrary algebra form an ideal inside the associating subalgebra: the manuscript's *society*. The proof runs through the two cases produced by gregariousness of $b$, transporting each back across the bracket by the associating hypotheses; the dual statement, with the new factor on the left, is a separate milestone.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §4.2 (p. 7): "Let b be gregarious, and associating. Suppose bc is defined, where c is also associating. Then bc is gregarious and associating. ... So the gregarious, associating elements of an algebra form an ideal in the subalgebra of associating elements, called its society."

import Definitions.Def_BalancedAlgebra_core

namespace BalancedAlgebra

open PartialAlgebra

theorem society_mul_right {A : Type*} (P : PartialAlgebra A) (b c e : A)
    (hbg : P.Gregarious b) (hb : P.Associating b) (hc : P.Associating c)
    (hbc : P.op b c = some e) : P.Gregarious e ∧ P.Associating e := by sorry

end BalancedAlgebra
