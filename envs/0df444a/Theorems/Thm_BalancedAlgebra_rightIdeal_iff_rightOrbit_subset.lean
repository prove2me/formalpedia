-- Prove2me | Theorems.Thm_BalancedAlgebra_rightIdeal_iff_rightOrbit_subset
-- name    : BalancedAlgebra.rightIdeal_iff_rightOrbit_subset
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-14T00:30:01.164247+00:00
-- url     : https://prove2.me/theorems/4bcfe7c3-7293-41ad-b35b-d11c62865be2
-- title:
--   Right ideals are exactly the orbit-closed subsets
-- statement:
--   Let $A$ carry a partial binary operation and let $B\subseteq A$ be an arbitrary subset. Recall that $B$ is a **right ideal** when $b\cdot a\in B$ for every $b\in B$ and every $a$ such that $b\cdot a$ is defined, and that the **right orbit** of $b$ is $bA=\{c:\exists a,\ b\cdot a=c\}$.
--
--   $$B \text{ is a right ideal} \iff \forall b\in B,\ bA\subseteq B.$$
--
--   This is the manuscript's remark that a subset is a right ideal precisely when it contains the right orbit of each of its elements. It is the reformulation used whenever an ideal is exhibited as a union of orbits, and the left-handed statement is its mirror image.
-- source:
--   Andrew Winkler, *Ideals in Balanced Algebras and the Genesis of Mathematics*, manuscript dated 20 March 2020, §1 (p. 2): "Evidently B is a right ideal if and only if it contains the right orbit of b whenever b is an element of B."

import Definitions.Def_BalancedAlgebra_core

namespace BalancedAlgebra

open PartialAlgebra

theorem rightIdeal_iff_rightOrbit_subset {A : Type*} (P : PartialAlgebra A) (B : Set A) :
    P.RightIdeal B ↔ ∀ b ∈ B, P.rightOrbit b ⊆ B := by sorry

end BalancedAlgebra
