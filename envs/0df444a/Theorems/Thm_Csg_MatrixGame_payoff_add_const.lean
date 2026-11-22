-- Prove2me | Theorems.Thm_Csg_MatrixGame_payoff_add_const
-- name    : Csg.MatrixGame.payoff_add_const
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:03:14.660097+00:00
-- url     : https://prove2.me/theorems/c279fae4-285f-4386-b2b5-fbbec9ab7201
-- title:
--   Matrix Game: payoff add const
-- statement:
--   **Added for the reachability-iterate convergence plan (see `PHASE0-NOTES.md`).** Shifting
--       every entry of a payoff matrix by the same constant shifts the payoff at any fixed strategy
--       pair by that constant -- both players' weights sum to `1`, so the shift factors straight out.
--       The per-state building block `value_add_const` below chains against.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L362-L378
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L362-L378

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.payoff_add_const {G G' : MatrixGame I J} (c : ℝ) (h : ∀ i j, G'.A i j = G.A i j + c)
    {x : I → ℝ} {y : J → ℝ} (hx : x ∈ stdSimplex ℝ I) (hy : y ∈ stdSimplex ℝ J) :
    G'.payoff x y = G.payoff x y + c := by sorry
