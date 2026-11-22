-- Prove2me | Theorems.Thm_Csg_MatrixGame_payoff_single_left
-- name    : Csg.MatrixGame.payoff_single_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:05:11.80431+00:00
-- url     : https://prove2.me/theorems/99d575fe-c6fc-4b34-8d26-c30e86b1711b
-- title:
--   Matrix Game: payoff single left
-- statement:
--   The column player's payoff against the pure row strategy `i` collapses to the bare sum
--       `∑ j, G.A i j * y j` -- symmetric counterpart of `payoff_single_right`, via
--       `payoff_eq_sum_mul` instead.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L698-L701
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L698-L701

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

theorem Csg.MatrixGame.payoff_single_left (i : I) (y : J → ℝ) :
    G.payoff (Pi.single i 1) y = ∑ j, G.A i j * y j := by sorry
