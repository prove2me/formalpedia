-- Prove2me | Theorems.Thm_FiniteMagmaE677_fixer_unique
-- name    : FiniteMagmaE677.fixer_unique
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-10T06:36:42.585236+00:00
-- url     : https://prove2.me/theorems/ab3cb982-cd64-4a98-a0e4-26f710b3244b
-- title:
--   E677 determines any fixer uniquely
-- statement:
--   Let $A$ be finite with arbitrary operation $\diamond$ satisfying E677. For $x,y\in A$,
--
--   $$y\diamond x=x\quad\Longrightarrow\quad y=(x\diamond x)\diamond x.$$
--
--   Thus the theorem determines the value of any fixer, conditional on its existence; it does not assert existence. Source: Equational Theories Project, online proof blueprint, Chapter 13, Lemma 13.1, https://teorth.github.io/equational_theories/blueprint/677-chapter.html, part (ii).
-- source:
--   Equational Theories Project, online proof blueprint, Chapter 13, Lemma 13.1, https://teorth.github.io/equational_theories/blueprint/677-chapter.html, part (ii)

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.fixer_unique {α : Type u} [Fintype α] (op : α → α → α)
    (h : FiniteMagmaE677.E677 op) (x y : α) (hfix : op y x = x) :
    y = op (op x x) x := by sorry
