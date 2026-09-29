-- Prove2me | Theorems.Thm_FiniteMagmaE677_cross_boundary_collision_propagates_to_left_successor
-- name    : FiniteMagmaE677.cross_boundary_collision_propagates_to_left_successor
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-11T05:11:12.051749+00:00
-- url     : https://prove2.me/theorems/6ebf77da-1ec1-4111-b970-0b1037749999
-- title:
--   A cross-boundary right-translation collision propagates to the next point of the left orbit
-- statement:
--   Fix an element $x$ and let $O_x=\{L_x^n(x):n\ge 0\}$ be its orbit under the left translation $L_x(z)=x\diamond z$. Assume E677, assume that $x$ has no right fixer, and assume that $A$ is the unique element outside $O_x$. For an orbit element $c$, prove
--
--   $$
--   c\diamond x=A\diamond x
--   \quad\Longrightarrow\quad
--   (x\diamond c)\diamond x=A\diamond x.
--   $$
--
--   Thus, in the no-fixer branch, a collision between $c$ and $A$ under right translation by $x$ propagates from $c$ to the next point $x\diamond c$ of the left orbit. No associativity, commutativity, or identity is assumed.
-- source:
--   Local propagation sub-goal isolated from the cross-boundary collision residual in docs/current/e677-closure-plan-2026-08-04.md, section 3, and docs/current/spine-refactoring-audit-2026-09-07.md, section 2; Equational Theories Project blueprint, Chapter 13; Bolan et al., arXiv:2512.07087v2, Section 8, Problem 8.1.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.cross_boundary_collision_propagates_to_left_successor
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x A : α)
    (hnofix : ¬ FiniteMagmaE677.HasFixerAt op x)
    (hA_notin : ¬ FiniteMagmaE677.InLeftOrbit op x A)
    (hA_unique : ∀ a : α, ¬ FiniteMagmaE677.InLeftOrbit op x a → a = A)
    (c : α) (hc : FiniteMagmaE677.InLeftOrbit op x c)
    (hcollision : op c x = op A x) :
    op (op x c) x = op A x := by sorry
