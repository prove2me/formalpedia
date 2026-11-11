-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_lemma_2_2
-- name    : FiniteGroupTesting.LinearQuery.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:55.439496+00:00
-- url     : https://prove2.me/theorems/2faa1603-83d7-40a1-a80e-68ebd4cc7c3b
-- title:
--   Lemma 2.2 — a regular action gives a group
-- statement:
--   Let $P\le\operatorname{Sym}(X)$ act regularly on the finite set $X$, and fix $e\in X$. Let $p_x$ be its unique element sending $e$ to $x$, and define
--
--   $$x\circ y=p_x(y).$$
--
--   This multiplication satisfies the group axioms with identity $e$. The map $x\mapsto p_x$ is bijective, sends $e$ to the identity and satisfies $p_{x\circ y}=p_xp_y$, so it is an isomorphism onto $P$. No pre-existing group structure on $X$ is assumed. This constructs the law needed after regularity is established.
--
--   Differences from the source: none.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 13, Lemma 2.2

import Definitions.Def_FiniteGroupTesting_LinearQuery_StoredActions

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery

/-- Lemma 2.2, p. 13. The multiplication is constructed from P, rather than assumed. -/
theorem lemma_2_2 {X : Type} [Fintype X] (P : Subgroup (Equiv.Perm X))
    (e : X) (hP : Regular P) :
    GroupLawAt (inducedLaw P e) e ∧
      Function.Bijective (representative P e) ∧
      representative P e e = 1 ∧
      ∀ x y : X, representative P e (inducedLaw P e x y) =
        representative P e x * representative P e y := by sorry

end FiniteGroupTesting.LinearQuery
