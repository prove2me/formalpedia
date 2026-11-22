-- Prove2me | Theorems.Thm_Csg_MatrixGame_abs_value_sub_le
-- name    : Csg.MatrixGame.abs_value_sub_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:45:55.622143+00:00
-- url     : https://prove2.me/theorems/2e06c912-a359-4389-9391-236b4070b644
-- title:
--   Matrix Game: abs value sub le
-- statement:
--   **The payoff.** `MatrixGame.value` is `1`-Lipschitz in the sup-norm on the payoff matrix --
--       the fact the reachability-iterate convergence plan actually needs (see `PHASE0-NOTES.md`):
--       once this lifts through `CSG.expect`/`stageValue` to the continuation `v`, it is exactly what
--       `ωScottContinuous (C.reachOp goal hr)` requires. Both directions of `value_le_add_of_forall_le`
--       (`G` against `G'`, then `G'` against `G`) assembled into one `abs`-valued statement via
--       `abs_le`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L425-L431
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L425-L431

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.abs_value_sub_le {G G' : MatrixGame I J} {ε : ℝ}
    (h : ∀ i j, |G'.A i j - G.A i j| ≤ ε) : |G'.value - G.value| ≤ ε := by sorry
