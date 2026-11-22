-- Prove2me | Theorems.Thm_Csg_MatrixGame_payoff_le_of_forall_le
-- name    : Csg.MatrixGame.payoff_le_of_forall_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:03:05.204494+00:00
-- url     : https://prove2.me/theorems/bbc947bc-db03-45be-8905-d9ae0b4ac8a4
-- title:
--   Matrix Game: payoff le of forall le
-- statement:
--   The payoff at any pair of mixed strategies is at most any constant bounding every matrix entry
--       -- a weighted average (nonnegative weights, each side's weights summing to `1`) of numbers `≤ c`
--       is itself `≤ c`. No optimality needed; `value_le_of_forall_le` below is a one-line corollary at
--       the optimal strategy pair.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L320-L330
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L320-L330

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.payoff_le_of_forall_le {x : I → ℝ} {y : J → ℝ} (hx : x ∈ stdSimplex ℝ I)
    (hy : y ∈ stdSimplex ℝ J) {c : ℝ} (h : ∀ i j, G.A i j ≤ c) :
    G.payoff x y ≤ c := by sorry
