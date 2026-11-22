-- Prove2me | Theorems.Thm_Csg_MatrixGame_value_row_optimal
-- name    : Csg.MatrixGame.value_row_optimal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:40:22.764317+00:00
-- url     : https://prove2.me/theorems/b4fe3055-fbc0-43f8-aeb7-13841930d986
-- title:
--   Matrix Game: value row optimal
-- statement:
--   The row player cannot lower the payoff below `value` by unilaterally deviating from
--       `optimalRow`, while the column player holds `optimalCol` fixed.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L211-L213
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L211-L213

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.value_row_optimal : ∀ p' ∈ stdSimplex ℝ I, G.value ≤ G.payoff p' G.optimalCol := by sorry
