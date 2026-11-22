-- Prove2me | Theorems.Thm_Csg_MatrixGame_le_payoff_of_forall_le
-- name    : Csg.MatrixGame.le_payoff_of_forall_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:03:08.766587+00:00
-- url     : https://prove2.me/theorems/74cff219-42c5-43ee-a439-49e53f1e59a9
-- title:
--   Matrix Game: le payoff of forall le
-- statement:
--   Symmetric counterpart of `payoff_le_of_forall_le`: the payoff is at least any constant bounded
--       above by every matrix entry.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L334-L344
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L334-L344

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.le_payoff_of_forall_le {x : I → ℝ} {y : J → ℝ} (hx : x ∈ stdSimplex ℝ I)
    (hy : y ∈ stdSimplex ℝ J) {c : ℝ} (h : ∀ i j, c ≤ G.A i j) :
    c ≤ G.payoff x y := by sorry
