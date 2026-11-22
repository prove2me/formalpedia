-- Prove2me | Theorems.Thm_Csg_MatrixGame_value_relabelRow
-- name    : Csg.MatrixGame.value_relabelRow
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:49:04.189173+00:00
-- url     : https://prove2.me/theorems/14358780-a47a-4ecd-b032-c0a3b1ea552f
-- title:
--   Matrix Game: value relabel Row
-- statement:
--   **The payoff.** `MatrixGame.value` doesn't change under a bijective relabelling of the row
--       player's action type: `G.optimalRow` pushed forward along `e` is still an optimal row strategy
--       for the relabelled game, against the very same `G.optimalCol`, so `value_unique` reads the
--       relabelled value off directly.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L526-L549
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L526-L549

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

theorem Csg.MatrixGame.value_relabelRow (e : I' ≃ I) : (G.relabelRow e).value = G.value := by sorry
