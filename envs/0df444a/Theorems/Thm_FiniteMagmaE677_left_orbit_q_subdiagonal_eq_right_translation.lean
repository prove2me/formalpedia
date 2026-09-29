-- Prove2me | Theorems.Thm_FiniteMagmaE677_left_orbit_q_subdiagonal_eq_right_translation
-- name    : FiniteMagmaE677.left_orbit_q_subdiagonal_eq_right_translation
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-15T04:33:57.531849+00:00
-- url     : https://prove2.me/theorems/1fdf219c-bb51-4fb8-b506-1cf623ae83c6
-- title:
--   The first orbit q-subdiagonal is right translation two steps later
-- statement:
--   Let $(\alpha,\diamond)$ be a finite magma satisfying E677: for all $p,q\in\alpha$,
--   $$p=q\diamond\bigl(p\diamond((q\diamond p)\diamond q)\bigr).$$
--   Fix $x\in\alpha$, write $L_x(z)=x\diamond z$, and let $c_n=L_x^{\,n}(x)$ be the points of the left orbit of $x$. For indices $i,j$ define the orbit $q$-term
--   $$q(i,j)=c_j\diamond\bigl((c_i\diamond c_j)\diamond c_i\bigr),$$
--   which by E677 satisfies $c_i\diamond q(i,j)=c_j$. Then for every $k\ge 0$, the first subdiagonal of $q$ is right translation by $x$ two orbit steps later:
--   $$q(k+1,k)=c_{k+2}\diamond x.$$
--
--   This identity turns statements about right translation $z\mapsto z\diamond x$ along the left orbit into statements about the explicit left-inverse terms $q(k+1,k)$. In particular, collisions of right translation on the orbit correspond index by index to collisions on the $q$-subdiagonal.
--
--   **Formalization Note** The orbit point $c_n$ is written `(op x)^[n] x`, and $q(k+1,k)$ is written out in full rather than through an auxiliary definition.
-- source:
--   Supporting lemma for the finite E677 to E255 formalization, mission 508ccd7b-8791-4bdf-883c-9a44bd760881; Equational Theories Project blueprint, Chapter 13, https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Bolan et al., arXiv:2512.07087v2, Section 8, Problem 8.1.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.left_orbit_q_subdiagonal_eq_right_translation
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x : α) (k : ℕ) :
    op ((op x)^[k] x)
        (op (op ((op x)^[k + 1] x) ((op x)^[k] x)) ((op x)^[k + 1] x)) =
      op ((op x)^[k + 2] x) x := by sorry
