-- Prove2me | Theorems.Thm_FiniteMagmaE677_unique_left_orbit_complement_escape_gives_fixer
-- name    : FiniteMagmaE677.unique_left_orbit_complement_escape_gives_fixer
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-11T02:09:50.900272+00:00
-- url     : https://prove2.me/theorems/84c353d1-7d95-4e7a-bd06-4b7aa8424dd0
-- title:
--   Right-translation escape with one element outside the left orbit gives a fixer
-- statement:
--   For an element $x$, let $O_x=\{L_x^n(x):n\ge 0\}$ be its orbit under the left translation $L_x(z)=x\diamond z$. Assume E677, assume $x\diamond x\ne x$, and assume exactly one element $A$ lies outside $O_x$. If right translation by $x$ sends some element of $O_x$ outside $O_x$, prove that $x$ has a right fixer: there is a $y$ such that $y\diamond x=x$. No associativity, commutativity, or identity is assumed.
-- source:
--   Semantic branch target from the finite E677 to E255 formalization, lean/E677/Spine/Gap1Closeout.lean, theorem e677_fixer_gap1_of_orbit_right_dip; Equational Theories Project blueprint, Chapter 13; Bolan et al., arXiv:2512.07087v2, Section 8, Problem 8.1.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.unique_left_orbit_complement_escape_gives_fixer
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x A : α) (hni : op x x ≠ x)
    (hA_notin : ¬ FiniteMagmaE677.InLeftOrbit op x A)
    (hA_unique : ∀ a : α, ¬ FiniteMagmaE677.InLeftOrbit op x a → a = A)
    (hescape : ∃ a : α,
      FiniteMagmaE677.InLeftOrbit op x a ∧
        ¬ FiniteMagmaE677.InLeftOrbit op x (op a x)) :
    FiniteMagmaE677.HasFixerAt op x := by sorry
