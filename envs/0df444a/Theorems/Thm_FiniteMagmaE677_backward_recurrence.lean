-- Prove2me | Theorems.Thm_FiniteMagmaE677_backward_recurrence
-- name    : FiniteMagmaE677.backward_recurrence
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-10T06:36:55.315946+00:00
-- url     : https://prove2.me/theorems/d4d2394d-0e3d-4162-bac9-c50cacd133e9
-- title:
--   E677 gives a backward recurrence
-- statement:
--   Let $A$ be finite with arbitrary operation $\diamond$ satisfying E677. For every $x,y\in A$,
--
--   $$x=(y\diamond x)\diamond\bigl((y\diamond(y\diamond x))\diamond y\bigr).$$
--
--   This is the backward-recurrence identity of Lemma 13.1(iii).
-- source:
--   Equational Theories Project, online proof blueprint, Chapter 13, Lemma 13.1, https://teorth.github.io/equational_theories/blueprint/677-chapter.html, part (iii)

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.backward_recurrence {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x y : α) :
    x = op (op y x) (op (op y (op y x)) y) := by sorry
