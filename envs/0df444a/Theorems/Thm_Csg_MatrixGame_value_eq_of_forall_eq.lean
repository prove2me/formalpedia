-- Prove2me | Theorems.Thm_Csg_MatrixGame_value_eq_of_forall_eq
-- name    : Csg.MatrixGame.value_eq_of_forall_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:50:31.736339+00:00
-- url     : https://prove2.me/theorems/6929323b-5eeb-4f46-b5e3-bcbcb3cd2697
-- title:
--   Matrix Game: value eq of forall eq
-- statement:
--   A constant payoff matrix has that constant as its value -- immediate from sandwiching `value`
--       between the same constant from both sides (`MatrixGameMonotone.lean`). Exactly what makes a
--       self-looping / deterministically-passing-through state's stage game trivial to evaluate below:
--       its payoff matrix doesn't depend on the joint action at all.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L63-L65
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L63-L65

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg Csg.MatrixGame
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [DecidableEq I]
  [DecidableEq J] (G : MatrixGame I J)

theorem Csg.MatrixGame.value_eq_of_forall_eq {c : ℝ} (h : ∀ i j, G.A i j = c) : G.value = c := by sorry
