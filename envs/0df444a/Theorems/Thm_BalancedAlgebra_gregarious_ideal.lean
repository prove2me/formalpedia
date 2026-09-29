-- Prove2me | Theorems.Thm_BalancedAlgebra_gregarious_ideal
-- name    : BalancedAlgebra.gregarious_ideal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T03:27:59.43062+00:00
-- url     : https://prove2.me/theorems/04385e33-2da3-475c-aec5-cb3c4370fbc5
-- title:
--   The gregarious ideal of an association
-- statement:
--   Let $A$ be an **association**: every element $b$ satisfies that, for all $a,c$, the products $(ab)c$ and $a(bc)$ are defined together and agree whenever both are defined. Call $b$ **gregarious** when, whenever $a\cdot b$ and $b\cdot c$ are both defined, at least one of $(ab)c$, $a(bc)$ is defined.
--
--   $$\{\,b\in A: b \text{ gregarious}\,\}\ \text{is a left ideal and a right ideal of } A.$$
--
--   This is the manuscript's **gregarious ideal**. Its role is structural: an association coinciding with its gregarious ideal is a **society**, so "society" becomes the assertion that this ideal is trivial by being everything — the same triviality device that yields simple groups and division rings elsewhere — and a quivered society is a category. The two halves are dual to each other, and each follows from the corresponding one-sided closure property of gregarious associating elements.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §4.2 (pp. 6–7): "In an association, the gregarious elements form an ideal; the gregarious ideal. An association which coincides with its gregarious ideal we call a society."

import Definitions.Def_BalancedAlgebra_core

namespace BalancedAlgebra

open PartialAlgebra

theorem gregarious_ideal {A : Type*} (P : PartialAlgebra A) (hP : P.IsAssociation) :
    P.LeftIdeal {b : A | P.Gregarious b} ∧ P.RightIdeal {b : A | P.Gregarious b} := by sorry

end BalancedAlgebra
