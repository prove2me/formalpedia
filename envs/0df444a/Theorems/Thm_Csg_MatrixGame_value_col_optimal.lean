-- Prove2me | Theorems.Thm_Csg_MatrixGame_value_col_optimal
-- name    : Csg.MatrixGame.value_col_optimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:40:25.188805+00:00
-- url     : https://prove2.me/theorems/9cd909c5-c427-46a7-81ce-538c5e479212
-- title:
--   Matrix Game: value col optimal
-- statement:
--   The column player cannot raise the payoff above `value` by unilaterally deviating from
--       `optimalCol`, while the row player holds `optimalRow` fixed.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L217-L219
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L217-L219

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.value_col_optimal : ∀ q' ∈ stdSimplex ℝ J, G.payoff G.optimalRow q' ≤ G.value := by sorry
