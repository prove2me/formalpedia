-- Prove2me | Theorems.Thm_Csg_MatrixGame_optimalCol_mem
-- name    : Csg.MatrixGame.optimalCol_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:40:24.042851+00:00
-- url     : https://prove2.me/theorems/7f38a521-129c-4ca9-8e00-cd5b5e8f7c4a
-- title:
--   Matrix Game: optimal Col mem
-- statement:
--   The Matrix Game construction uses the optimal Col mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L205-L207
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L205-L207

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.optimalCol_mem : G.optimalCol ∈ stdSimplex ℝ J := by sorry
