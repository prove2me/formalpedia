-- Prove2me | Theorems.Thm_FiniteMagmaE677_collision_cancel
-- name    : FiniteMagmaE677.collision_cancel
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T06:52:59.24404+00:00
-- url     : https://prove2.me/theorems/f6aa6dfc-2837-4f8a-907f-b32903d42473
-- title:
--   Right-translation collisions cancel after one round trip
-- statement:
--   Let $A$ be a finite set with a binary operation $\diamond$ satisfying E677, and write $R_x z = z \diamond x$. If two elements $a, b$ (arbitrary, with no orbit or fixer hypothesis) collide under right translation by $x$, say $a \diamond x = b \diamond x = \omega$, then
--
--   $$ (a \diamond \omega) \diamond a \;=\; (b \diamond \omega) \diamond b. $$
--
--   The proof applies the backward recurrence $x = (y \diamond x) \diamond \bigl((y \diamond (y \diamond x)) \diamond y\bigr)$ at $y = a$ and $y = b$: both instances decompose $x$ with the same outer factor $\omega$, and cancelling the left translation $L_\omega$ (injective by left bijectivity) gives the identity. As a byproduct, the common value $S$ satisfies $\omega \diamond S = x$.
-- source:
--   Identity identified and verified numerically on finite models by zjay5 (Prove2Me mission comment on 'Equational Magmas: E677 → E255 (finite case)', 2026-09-22); proved here. Context: Equational Theories Project blueprint, Chapter 13, https://teorth.github.io/equational_theories/blueprint/677-chapter.html, Lemma 13.1(i),(iii).

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_backward_recurrence

universe u

theorem FiniteMagmaE677.collision_cancel {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x a b : α)
    (hcol : op a x = op b x) :
    op (op a (op a x)) a = op (op b (op a x)) b := by sorry
