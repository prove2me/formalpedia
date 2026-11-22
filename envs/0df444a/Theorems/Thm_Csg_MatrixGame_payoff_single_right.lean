-- Prove2me | Theorems.Thm_Csg_MatrixGame_payoff_single_right
-- name    : Csg.MatrixGame.payoff_single_right
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:05:14.172861+00:00
-- url     : https://prove2.me/theorems/dd4b39d2-0a0c-4c25-ab5f-55e0a3c9244a
-- title:
--   Matrix Game: payoff single right
-- statement:
--   The row player's payoff against the pure column strategy `j` collapses to the bare sum
--       `∑ i, x i * G.A i j` -- `payoff_eq_sum_mul'` pulls the column strategy out as an outer sum,
--       over which `Pi.single j 1` picks out exactly the `j`-th term.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L690-L693
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L690-L693

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

theorem Csg.MatrixGame.payoff_single_right (x : I → ℝ) (j : J) :
    G.payoff x (Pi.single j 1) = ∑ i, x i * G.A i j := by sorry
