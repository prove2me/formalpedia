-- Prove2me | Theorems.Thm_Csg_MatrixGame_value_le_of_forall_le
-- name    : Csg.MatrixGame.value_le_of_forall_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:48:17.102511+00:00
-- url     : https://prove2.me/theorems/7e4408c0-4534-47b0-a86b-92435f2701b6
-- title:
--   Matrix Game: value le of forall le
-- statement:
--   **The payoff.** The game's value lies between any two constants bounding all its matrix
--       entries -- both halves of the sandwich the reachability Bellman operator will need to stay
--       inside `[0, 1]`. Direct corollaries of `payoff_le_of_forall_le`/`le_payoff_of_forall_le` at the
--       optimal strategy pair, since `value` is *defined* as `payoff optimalRow optimalCol`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L350-L352
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L350-L352

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.value_le_of_forall_le {c : ℝ} (h : ∀ i j, G.A i j ≤ c) : G.value ≤ c := by sorry
