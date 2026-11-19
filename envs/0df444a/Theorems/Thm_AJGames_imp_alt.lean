-- Prove2me | Theorems.Thm_AJGames_imp_alt
-- name    : AJGames.imp_alt
-- status  : Proved
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:31:17.336323+00:00
-- url     : https://prove2.me/theorems/8f9a3556-bce7-4804-a6fe-f3091c52a283
-- title:
--   Positions of $A\multimap B$ alternate
-- statement:
--   For all games $A,B$, every position of $A\multimap B$ alternates between Player and Opponent moves.
--
--   It follows from the tensor's alternation clause alone, without using that the positions of $A$ and $B$ alternate.
-- source:
--   S. Abramsky, R. Jagadeesan, Games and full completeness for multiplicative linear logic, J. Symbolic Logic 59(2) (1994) 543-574, https://arxiv.org/abs/1311.6057, §3.2 (linear implication)

import Mathlib
import Definitions.Def_AJGames_Game
import Definitions.Def_AJGames_Tensor

namespace AJGames

/-- **Positions of `A ⊸ B` alternate by T1 alone** (Abramsky and Jagadeesan, *Games and Full Completeness for Multiplicative Linear Logic*, J. Symbolic Logic 59(2) (1994), §3.2: `A ⊸ B := (A ⊗ B⊥)⊥`). No alternation of `A` or `B` is used.
AJ axioms used: T1 only. -/
theorem imp_alt (A B : Game) {s : List (Game.imp A B).M} (h : s ∈ (Game.imp A B).pos) :
    Alt (Game.imp A B).lab s := by sorry

end AJGames
