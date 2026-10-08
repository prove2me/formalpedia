-- Prove2me | Theorems.Thm_FiniteMagmaE677_linear_collision_injective
-- name    : FiniteMagmaE677.linear_collision_injective
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T12:08:29.453185+00:00
-- url     : https://prove2.me/theorems/c8a75685-12ed-40d0-a04b-3f88e3f65cc2
-- title:
--   Right-translation collisions that force left agreement imply injectivity
-- statement:
--   Let $A$ be a finite set with a binary operation $\diamond$ satisfying E677, and write $L_y z = y \diamond z$, $R_y z = z \diamond y$. Suppose that right-translation collisions at the fixed element $x$ force full left-translation agreement:
--
--   $$R_x y = R_x y' \implies L_y = L_{y'}.$$
--
--   Then right translation $R_x$ is injective: $R_x y = R_x y'$ implies $y = y'$.
--
--   Writing $p = y \diamond x = y' \diamond x$, E677 at $(x,y)$ and $(x,y')$ reads $x = L_y (L_x (L_p\, y))$ and $x = L_{y'} (L_x (L_p\, y'))$; since the outer factors agree by the hypothesis, cancelling the three injective left translations yields $y = y'$. This is the magma-level core of the blueprint's "no linear counterexamples" lemma for Chapter 13 of the Equational Theories Project.
-- source:
--   Equational Theories Project, online proof blueprint, Chapter 13 (677), linear-model lemma, https://teorth.github.io/equational_theories/blueprint/677-chapter.html; magma-level abstraction and Lean proof contributed here.

import Definitions.Def_FiniteMagmaE677
import Theorems.Thm_FiniteMagmaE677_left_bijective

universe u

theorem FiniteMagmaE677.linear_collision_injective {α : Type u} [Fintype α]
    (op : α → α → α) (h : FiniteMagmaE677.E677 op) (x : α)
    (hlin : ∀ y y' z : α, op y x = op y' x → op y z = op y' z) :
    ∀ y y' : α, op y x = op y' x → y = y' := by sorry
