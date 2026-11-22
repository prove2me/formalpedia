-- Prove2me | Theorems.Thm_Csg_MatrixGame_value_isGreatest_colLPFeasible
-- name    : Csg.MatrixGame.value_isGreatest_colLPFeasible
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:49:25.859045+00:00
-- url     : https://prove2.me/theorems/d9f637fb-5296-455c-bac5-7de1635a74b4
-- title:
--   Matrix Game: value is Greatest col LPFeasible
-- statement:
--   **The payoff, dual side.** `G.value` is exactly the *greatest* element of `colLPFeasible G` --
--       the mirror-image LP, from the maximising player's side. Membership comes from
--       `value_row_optimal` applied at each pure row strategy (via `payoff_single_left`); the
--       upper-bound half is `payoff_ge_of_row_ge` chained with `value_col_optimal`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L764-L771
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L764-L771

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

theorem Csg.MatrixGame.value_isGreatest_colLPFeasible : IsGreatest (G.colLPFeasible) G.value := by sorry
