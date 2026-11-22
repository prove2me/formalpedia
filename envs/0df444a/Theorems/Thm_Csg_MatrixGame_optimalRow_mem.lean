-- Prove2me | Theorems.Thm_Csg_MatrixGame_optimalRow_mem
-- name    : Csg.MatrixGame.optimalRow_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:40:19.324333+00:00
-- url     : https://prove2.me/theorems/c99805f9-2490-4f02-bb6f-3f2077aefcb9
-- title:
--   Matrix Game: optimal Row mem
-- statement:
--   The Matrix Game construction uses the optimal Row mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L201-L203
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L201-L203

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.optimalRow_mem : G.optimalRow ∈ stdSimplex ℝ I := by sorry
