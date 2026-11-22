-- Prove2me | Theorems.Thm_Csg_MatrixGame_value_relabelCol
-- name    : Csg.MatrixGame.value_relabelCol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:53:33.237071+00:00
-- url     : https://prove2.me/theorems/f2559ce9-fcfb-460d-9aa8-b40a865f55fa
-- title:
--   Matrix Game: value relabel Col
-- statement:
--   **The payoff.** `MatrixGame.value` doesn't change under a bijective relabelling of the column
--       player's action type -- mirror of `value_relabelRow`, with `G.optimalRow` held fixed this time
--       and `G.optimalCol` pushed forward along `e`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L608-L631
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L608-L631

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

theorem Csg.MatrixGame.value_relabelCol (e : J' ≃ J) : (G.relabelCol e).value = G.value := by sorry
