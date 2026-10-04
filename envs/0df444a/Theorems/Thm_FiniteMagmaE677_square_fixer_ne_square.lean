-- Prove2me | Theorems.Thm_FiniteMagmaE677_square_fixer_ne_square
-- name    : FiniteMagmaE677.square_fixer_ne_square
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T09:55:55.813661+00:00
-- url     : https://prove2.me/theorems/a5d385af-a164-457b-b4a6-0d6c016b8ea1
-- title:
--   The square of an element is not its own fixer
-- statement:
--   Let $A$ be a finite set with a binary operation $\diamond$ satisfying E677. If $s$ is a fixer of $b$ (i.e. $s \diamond b = b$) and the square of $b$ is that fixer, $b \diamond b = s$, then $b$ is idempotent, $b \diamond b = b$ (and hence $s = b$). Equivalently: a fixer $s \neq b$ of a non-idempotent element $b$ is never the square $b \diamond b$.
--
--   Writing $\omega = b \diamond s$, the backward recurrence at $(b, s)$, rewritten with $s \diamond b = b$, gives $b = b \diamond \omega$. The left translation $L_b$ then cycles
--   $$ b \longmapsto s \longmapsto \omega \longmapsto b,$$
--   so $L_b^3 b = b$, and the period-three theorem forces $b \diamond b = b$.
-- source:
--   Original result proved in this submission, in the context of the Prove2Me mission 'Equational Magmas: E677 → E255 (finite case)'. Method: closing a length-three cycle under L_b and applying no_left_period_three.

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_backward_recurrence
import Theorems.Thm_FiniteMagmaE677_no_left_period_three

universe u

theorem FiniteMagmaE677.square_fixer_ne_square {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (s b : α)
    (hs : op s b = b) (hsq : op b b = s) : op b b = b := by sorry
