-- Prove2me | Theorems.Thm_Csg_MatrixGame_value_add_const
-- name    : Csg.MatrixGame.value_add_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:53:34.105971+00:00
-- url     : https://prove2.me/theorems/5eecaeb8-81c5-4099-8d6c-ab01b645363f
-- title:
--   Matrix Game: value add const
-- statement:
--   **The payoff.** Shifting every entry of a payoff matrix by a constant shifts the *value* by
--       that same constant -- `G`'s own optimal strategy pair still witnesses a saddle point of the
--       shifted game `G'` (`payoff_add_const` turns each of `G`'s no-unilateral-improvement facts into
--       `G'`'s), so `value_unique` pins `G'`'s value down to `G.value + c` on the nose, rather than
--       just bounding it. Together with `value_mono`, this is what makes `MatrixGame.value` a genuine
--       Lipschitz (not just monotone) function of the payoff matrix -- see `abs_value_sub_le` below.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L386-L403
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L386-L403

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)

theorem Csg.MatrixGame.value_add_const {G G' : MatrixGame I J} (c : ℝ) (h : ∀ i j, G'.A i j = G.A i j + c) :
    G'.value = G.value + c := by sorry
