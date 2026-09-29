-- Prove2me | Theorems.Thm_FiniteMagmaE677_exact_base_rows_give_fixer
-- name    : FiniteMagmaE677.exact_base_rows_give_fixer
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-15T04:33:56.952503+00:00
-- url     : https://prove2.me/theorems/9ebacecf-0cb1-46b1-89ca-4153bac6cdab
-- title:
--   Seven exact-base table entries force E255 at a point
-- statement:
--   Let $(\alpha,\diamond)$ be a finite magma satisfying E677: for all $p,q\in\alpha$,
--   $$p=q\diamond\bigl(p\diamond((q\diamond p)\diamond q)\bigr).$$
--   Let $x,A,c_1,c_3,c_4\in\alpha$ satisfy the seven table entries
--
--   1. $x\diamond x=c_1$;
--   2. $x\diamond c_3=c_4$;
--   3. $c_1\diamond x=c_4$;
--   4. $A\diamond(A\diamond x)=A$;
--   5. $A\diamond A=c_1$;
--   6. $A\diamond x=c_3$;
--   7. $c_3\diamond c_3=c_1$.
--
--   Then E255 holds at $x$:
--   $$((x\diamond x)\diamond x)\diamond x=x.$$
--
--   The seven entries are the exact-base pattern observed at orbit size six with one element $A$ outside the left orbit of $x$, where $c_n$ denotes the $n$-th point of that orbit. The theorem shows that the pattern alone forces a right fixer of $x$, namely $(x\diamond x)\diamond x$, with no orbit, period, or outsider-uniqueness hypothesis. It closes every finite E677 context in which these seven entries occur.
--
--   **Formalization Note** The five elements are arbitrary; no distinctness among them is assumed. The names $c_1,c_3,c_4$ record their role in the orbit-size-six pattern and are not tied to an orbit in the statement.
-- source:
--   Supporting lemma for the finite E677 to E255 formalization, mission 508ccd7b-8791-4bdf-883c-9a44bd760881; Equational Theories Project blueprint, Chapter 13, https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Bolan et al., arXiv:2512.07087v2, Section 8, Problem 8.1.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.exact_base_rows_give_fixer
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x A c1 c3 c4 : α)
    (hxx : op x x = c1)
    (hxc3 : op x c3 = c4)
    (hc1x : op c1 x = c4)
    (hA_Ax : op A (op A x) = A)
    (hAA : op A A = c1)
    (hAx : op A x = c3)
    (hc3c3 : op c3 c3 = c1) :
    op (op (op x x) x) x = x := by sorry
