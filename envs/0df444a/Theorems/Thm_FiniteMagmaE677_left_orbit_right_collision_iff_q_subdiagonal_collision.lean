-- Prove2me | Theorems.Thm_FiniteMagmaE677_left_orbit_right_collision_iff_q_subdiagonal_collision
-- name    : FiniteMagmaE677.left_orbit_right_collision_iff_q_subdiagonal_collision
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-15T04:33:59.798967+00:00
-- url     : https://prove2.me/theorems/812c8c8b-9d33-492c-9400-0c3a8a9e20c1
-- title:
--   Right-translation collisions on the left orbit are q-subdiagonal collisions
-- statement:
--   Let $(\alpha,\diamond)$ be a finite magma satisfying E677: for all $p,q\in\alpha$,
--   $$p=q\diamond\bigl(p\diamond((q\diamond p)\diamond q)\bigr).$$
--   Fix $x\in\alpha$, write $L_x(z)=x\diamond z$, let $c_n=L_x^{\,n}(x)$, and define
--   $$q(i,j)=c_j\diamond\bigl((c_i\diamond c_j)\diamond c_i\bigr).$$
--   Then for all indices $i,j\ge 0$,
--   $$c_{i+2}\diamond x=c_{j+2}\diamond x\quad\Longleftrightarrow\quad q(i+1,i)=q(j+1,j).$$
--
--   This is the indexed normalization of right-translation collisions on the left orbit: a collision between the orbit points $c_{i+2}$ and $c_{j+2}$ under $z\mapsto z\diamond x$ holds exactly when the corresponding first-subdiagonal $q$-terms coincide. The indices are preserved; no reduction modulo a period is made.
--
--   **Formalization Note** The orbit point $c_n$ is written `(op x)^[n] x`, and the $q$-terms are written out in full. The statement concerns the orbit points with index at least two.
-- source:
--   Supporting lemma for the finite E677 to E255 formalization, mission 508ccd7b-8791-4bdf-883c-9a44bd760881; Equational Theories Project blueprint, Chapter 13, https://teorth.github.io/equational_theories/blueprint/677-chapter.html; Bolan et al., arXiv:2512.07087v2, Section 8, Problem 8.1.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.left_orbit_right_collision_iff_q_subdiagonal_collision
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x : α) (i j : ℕ) :
    op ((op x)^[i + 2] x) x = op ((op x)^[j + 2] x) x ↔
      op ((op x)^[i] x)
          (op (op ((op x)^[i + 1] x) ((op x)^[i] x)) ((op x)^[i + 1] x)) =
        op ((op x)^[j] x)
          (op (op ((op x)^[j + 1] x) ((op x)^[j] x)) ((op x)^[j + 1] x)) := by sorry
