-- Prove2me | Theorems.Thm_Csg_MatrixGame_payoff_ge_of_row_ge
-- name    : Csg.MatrixGame.payoff_ge_of_row_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:05:36.817328+00:00
-- url     : https://prove2.me/theorems/182e1d8b-f43c-4322-bde7-bf7935387809
-- title:
--   Matrix Game: payoff ge of row ge
-- statement:
--   **The row-side bound.** If every row's payoff against a fixed column strategy `y` is at least
--       `m`, then *every* mixed row strategy's payoff against `y` is at least `m` too -- `payoff (·) y`
--       is a weighted average of the per-row numbers `∑ j, G.A i j * y j`, and a weighted average
--       (nonnegative weights summing to `1`) of numbers each `≥ m` is itself `≥ m`. The one half of
--       `value_isGreatest_colLPFeasible`'s lower-bound direction that isn't already established
--       above.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L709-L719
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L709-L719

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

theorem Csg.MatrixGame.payoff_ge_of_row_ge (y : J → ℝ) (m : ℝ) (h : ∀ i, m ≤ ∑ j, G.A i j * y j) :
    ∀ x ∈ stdSimplex ℝ I, m ≤ G.payoff x y := by sorry
