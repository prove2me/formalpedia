-- Prove2me | Theorems.Thm_FiniteMagmaE677_two_left_orbit_complement_elements_escape_gives_fixer
-- name    : FiniteMagmaE677.two_left_orbit_complement_elements_escape_gives_fixer
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-11T02:09:52.227719+00:00
-- url     : https://prove2.me/theorems/db348bf7-0cc9-4564-be06-28795716dde4
-- title:
--   Right-translation escape with two elements outside the left orbit gives a fixer
-- statement:
--   For an element $x$, let $O_x=\{L_x^n(x):n\ge 0\}$ be its orbit under the left translation $L_x(z)=x\diamond z$. Assume E677, assume $x\diamond x\ne x$, and assume that at least two distinct elements lie outside $O_x$. If right translation by $x$ sends some element of $O_x$ outside $O_x$, prove that $x$ has a right fixer: there is a $y$ such that $y\diamond x=x$. No associativity, commutativity, or identity is assumed.
-- source:
--   Semantic branch target from the finite E677 to E255 formalization, lean/E677/Spine/D7NonFullCore.lean, theorem e677_fixer_two_outsiders_of_orbit_right_dip; Equational Theories Project blueprint, Chapter 13; Bolan et al., arXiv:2512.07087v2, Section 8, Problem 8.1.

import Definitions.Def_FiniteMagmaE677

universe u

theorem FiniteMagmaE677.two_left_orbit_complement_elements_escape_gives_fixer
    {α : Type u} [Fintype α] (op : α → α → α) (h : FiniteMagmaE677.E677 op)
    (x : α) (hni : op x x ≠ x)
    (htwo : ∃ a b : α,
      a ≠ b ∧
        ¬ FiniteMagmaE677.InLeftOrbit op x a ∧
          ¬ FiniteMagmaE677.InLeftOrbit op x b)
    (hescape : ∃ a : α,
      FiniteMagmaE677.InLeftOrbit op x a ∧
        ¬ FiniteMagmaE677.InLeftOrbit op x (op a x)) :
    FiniteMagmaE677.HasFixerAt op x := by sorry
