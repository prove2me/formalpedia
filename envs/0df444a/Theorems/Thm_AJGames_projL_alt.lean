-- Prove2me | Theorems.Thm_AJGames_projL_alt
-- name    : AJGames.projL_alt
-- status  : Proved
-- author  : @martelus trismortuus
-- created : 2026-11-18T15:31:53.62422+00:00
-- url     : https://prove2.me/theorems/ea79575c-d916-4160-871a-4fce8a748a30
-- title:
--   Restrictions of tensor plays alternate
-- statement:
--   Let $s$ be a sequence of moves of $A\otimes B$ in which consecutive moves have different labels and every change of component is an Opponent move. Then the restriction $s{\restriction}A$ alternates.
--
--   This is the key observation behind the comparison of the AJ tensor with Conway's sum.
-- source:
--   S. Abramsky, R. Jagadeesan, Games and full completeness for multiplicative linear logic, J. Symbolic Logic 59(2) (1994) 543-574, https://arxiv.org/abs/1311.6057, §6.1, Proposition 17 (the observation used in its proof)

import Mathlib
import Definitions.Def_AJGames_Game
import Definitions.Def_AJGames_Tensor

namespace AJGames

universe u

/-- **Projection of a tensor sequence is alternating** (Abramsky and Jagadeesan, *Games and Full Completeness for Multiplicative Linear Logic*, J. Symbolic Logic 59(2) (1994), §3.2, the observation behind the tensor being a game; used in Proposition 17). In a sequence satisfying the tensor clauses T1 and T2 (only Opponent switches component) the restriction to the left component is strictly alternating, with no assumption that the components' own positions alternate.
AJ axioms used: T1, T2. -/
theorem projL_alt {α β : Type u} (la : α → Pl) (lb : β → Pl) :
    ∀ s : List (α ⊕ β), List.IsChain (TR la lb) s → Alt la (projL s) := by sorry

end AJGames
