-- Prove2me | Theorems.Thm_Csg_MatrixGame_payoff_le_of_col_le
-- name    : Csg.MatrixGame.payoff_le_of_col_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:06:04.316346+00:00
-- url     : https://prove2.me/theorems/e0ca286b-442f-4fee-b820-ed9849cee263
-- title:
--   Matrix Game: payoff le of col le
-- statement:
--   **The column-side bound.** Mirror of `payoff_ge_of_row_ge`: if every column's payoff against a
--       fixed row strategy `x` is at most `m`, so is every mixed column strategy's payoff against `x`.
--       The one half of `value_isLeast_rowLPFeasible`'s upper-bound direction that isn't already
--       established above.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L725-L732
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L725-L732

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

theorem Csg.MatrixGame.payoff_le_of_col_le (x : I → ℝ) (m : ℝ) (h : ∀ j, (∑ i, x i * G.A i j) ≤ m) :
    ∀ y ∈ stdSimplex ℝ J, G.payoff x y ≤ m := by sorry
