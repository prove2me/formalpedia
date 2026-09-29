-- Prove2me | Theorems.Thm_FiniteMagmaE677_left_bijective
-- name    : FiniteMagmaE677.left_bijective
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-10T06:36:32.042488+00:00
-- url     : https://prove2.me/theorems/c3662c32-2139-496f-9e3f-f293127a8081
-- title:
--   E677 forces every left multiplication to be bijective
-- statement:
--   Let $A$ be a finite (possibly empty) type with arbitrary total operation $\diamond:A\times A\to A$. If E677 holds, then
--
--   $$\forall y\in A,\quad (x\mapsto y\diamond x)\text{ is bijective}.$$
--
--   This is the left-multiplication statement corresponding to part (i) of Lemma 13.1.
-- source:
--   Equational Theories Project, online proof blueprint, Chapter 13, Lemma 13.1, https://teorth.github.io/equational_theories/blueprint/677-chapter.html, part (i)

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.left_bijective {α : Type u} [Fintype α] (op : α → α → α)
    (h : FiniteMagmaE677.E677 op) (y : α) : Function.Bijective (op y) := by sorry
