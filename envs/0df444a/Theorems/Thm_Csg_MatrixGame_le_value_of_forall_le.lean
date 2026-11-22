-- Prove2me | Theorems.Thm_Csg_MatrixGame_le_value_of_forall_le
-- name    : Csg.MatrixGame.le_value_of_forall_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:48:29.112156+00:00
-- url     : https://prove2.me/theorems/0d95c37e-5759-4682-bfb4-429868e308f3
-- title:
--   Matrix Game: le value of forall le
-- statement:
--   The Matrix Game construction uses the le value of forall le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L354-L356
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L354-L356

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.le_value_of_forall_le {c : ℝ} (h : ∀ i j, c ≤ G.A i j) : c ≤ G.value := by sorry
