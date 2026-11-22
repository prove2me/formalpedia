-- Prove2me | Theorems.Thm_Csg_MatrixGame_value_le_add_of_forall_le
-- name    : Csg.MatrixGame.value_le_add_of_forall_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:03:48.1678+00:00
-- url     : https://prove2.me/theorems/647b6a6b-4dd4-4391-b275-41e51278e5d0
-- title:
--   Matrix Game: value le add of forall le
-- statement:
--   One direction of the Lipschitz bound: if `G'`'s entries never exceed `G`'s by more than `ε`,
--       `G'`'s value doesn't either. Assembled from `value_mono` (comparing `G'` against the *shifted*
--       game `fun i j => G.A i j + ε`) and `value_add_const` (identifying that shifted game's value as
--       `G.value + ε`) -- monotonicity plus the shift fact together give continuity, which neither
--       alone would.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L410-L417
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L410-L417

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.value_le_add_of_forall_le {G G' : MatrixGame I J} {ε : ℝ}
    (h : ∀ i j, G'.A i j ≤ G.A i j + ε) : G'.value ≤ G.value + ε := by sorry
