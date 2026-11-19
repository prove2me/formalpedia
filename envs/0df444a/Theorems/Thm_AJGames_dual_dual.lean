-- Prove2me | Theorems.Thm_AJGames_dual_dual
-- name    : AJGames.dual_dual
-- status  : Proved
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:30:36.436376+00:00
-- url     : https://prove2.me/theorems/0e45c2f5-23e2-4932-a750-f67eeb2dd263
-- title:
--   Double negation $A^{\perp\perp}=A$
-- statement:
--   For every game $A$, the dual of the dual of $A$ is $A$ itself:
--   $$A^{\perp\perp}=A.$$
--   This is a sanity check of the definition of duality.
-- source:
--   S. Abramsky, R. Jagadeesan, Games and full completeness for multiplicative linear logic, J. Symbolic Logic 59(2) (1994) 543-574, https://arxiv.org/abs/1311.6057, §3.2 ('clearly A⊥⊥ = A')

import Mathlib
import Definitions.Def_AJGames_Game

namespace AJGames

/-- **Double negation** `A⊥⊥ = A` (Abramsky and Jagadeesan, *Games and Full Completeness for Multiplicative Linear Logic*, J. Symbolic Logic 59(2) (1994), §3.2: "clearly `A⊥⊥ = A`").
AJ axioms used: G1, G2, G3 only (the fields of `Game`); no tensor axiom. -/
theorem dual_dual (A : Game) : A.dual.dual = A := by sorry

end AJGames
