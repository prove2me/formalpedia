-- Prove2me | Theorems.Thm_FiniteMagmaE677_unique_left_orbit_complement_collision_gives_fixer
-- name    : FiniteMagmaE677.unique_left_orbit_complement_collision_gives_fixer
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-11T03:25:46.543442+00:00
-- url     : https://prove2.me/theorems/575f60d1-4022-47be-be16-f537368a5d24
-- title:
--   A right-translation collision across a one-element left-orbit complement gives a fixer
-- statement:
--   For an element $x$, let $O_x=\{L_x^n(x):n\ge 0\}$ be its orbit under the left translation $L_x(z)=x\diamond z$. Assume E677, assume $x\diamond x\ne x$, and assume exactly one element $A$ lies outside $O_x$. If right translation by $x$ has a collision between $A$ and an element of $O_x$, prove that $x$ has a right fixer: there is a $y$ such that $y\diamond x=x$. No associativity, commutativity, or identity is assumed.
-- source:
--   Cross-boundary collision residual recommended by the finite E677 to E255 closure plan, docs/current/e677-closure-plan-2026-08-04.md, section 3, and docs/current/spine-refactoring-audit-2026-09-07.md, section 2; Equational Theories Project blueprint, Chapter 13; Bolan et al., arXiv:2512.07087v2, Section 8, Problem 8.1.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.unique_left_orbit_complement_collision_gives_fixer
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x A : α) (hni : op x x ≠ x)
    (hA_notin : ¬ FiniteMagmaE677.InLeftOrbit op x A)
    (hA_unique : ∀ a : α, ¬ FiniteMagmaE677.InLeftOrbit op x a → a = A)
    (hcollision : ∃ a : α,
      FiniteMagmaE677.InLeftOrbit op x a ∧ op a x = op A x) :
    FiniteMagmaE677.HasFixerAt op x := by sorry
