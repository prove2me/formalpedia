-- Prove2me | Theorems.Thm_Csg_MatrixGame_value_isLeast_rowLPFeasible
-- name    : Csg.MatrixGame.value_isLeast_rowLPFeasible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:49:07.903794+00:00
-- url     : https://prove2.me/theorems/32f3eca6-2e4a-40f9-a394-0d38b0c1c627
-- title:
--   Matrix Game: value is Least row LPFeasible
-- statement:
--   **The payoff, primal side.** `G.value` is exactly the *least* element of `rowLPFeasible G` --
--       the textbook LP for a zero-sum game's value, from the minimising player's side. Membership
--       comes from `value_col_optimal` applied at each pure column strategy in turn (via
--       `payoff_single_right`); the lower-bound half is `payoff_le_of_col_le` chained with
--       `value_row_optimal`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L751-L758
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L751-L758

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']
variable {J' : Type*} [Fintype J'] [Nonempty J'] [DecidableEq J']

theorem Csg.MatrixGame.value_isLeast_rowLPFeasible : IsLeast (G.rowLPFeasible) G.value := by sorry
