-- Prove2me | Theorems.Thm_FiniteMagmaE677_no_left_period_three
-- name    : FiniteMagmaE677.no_left_period_three
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T07:37:57.979725+00:00
-- url     : https://prove2.me/theorems/723d58bc-6c72-4650-9de3-0613f570dae4
-- title:
--   No element of a finite E677 magma has left-orbit period exactly three
-- statement:
--   Let $A$ be a finite set with a binary operation $\diamond$ satisfying E677 and let $L_x z = x \diamond z$. No element has forward orbit under $L_x$ of exact period three: if $x = L_x^3 x$, then already $x \diamond x = x$. Together with the period-two theorem, every non-idempotent element of a finite E677 magma has left orbit of length at least four.
--
--   Write $z_1 = x \diamond x$ and $z_2 = x \diamond z_1$. The proof derives the chain
--   $$ z_1 \diamond x = z_1, \qquad z_2 \diamond z_1 = z_1, \qquad z_2 = (z_1 \diamond z_1) \diamond z_1, $$
--   $$ x = z_1 \diamond z_2, \qquad z_1 \diamond z_1 = z_1, \qquad z_2 \diamond x = z_1, \qquad z_1 \diamond z_1 = x, $$
--   where the steps use E677 at $(x,x)$, $(z_2,x)$, $(x,z_1)$, $(z_1,x)$, fixer uniqueness at $z_1$, the backward recurrence at $(x, z_1)$, and the collision cancellation identity for the pair $x, z_1$ (which collide since $x \diamond x = z_1 = z_1 \diamond x$). The last two identities give $x = z_1 = x \diamond x$.
-- source:
--   Original result proved in this submission, in the context of the Prove2Me mission 'Equational Magmas: E677 → E255 (finite case)'; cf. Equational Theories Project blueprint Chapter 13, https://teorth.github.io/equational_theories/blueprint/677-chapter.html.

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective
import Theorems.Thm_FiniteMagmaE677_backward_recurrence
import Theorems.Thm_FiniteMagmaE677_fixer_unique
import Theorems.Thm_FiniteMagmaE677_collision_cancel

universe u

theorem FiniteMagmaE677.no_left_period_three {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x : α)
    (hper : op x (op x (op x x)) = x) : op x x = x := by sorry
