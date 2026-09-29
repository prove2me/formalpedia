-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacentHalfTwistConfig_two_child_v1
-- name    : BraidsLinksMCG.adjacentHalfTwistConfig_two_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T21:27:35.705009+00:00
-- url     : https://prove2.me/theorems/55afc2d5-aa26-43ac-816b-e0a537613db1
-- title:
--   Two adjacent half-twist periods return the ordered configuration
-- statement:
--   After two half-twist periods on the final adjacent pair, the ordered configuration returns pointwise to the standard base configuration. This is the endpoint fact needed to regard the full twist as a loop before identifying its braid class.
-- source:
--   Source-faithful prerequisite for BraidsLinksMCG.standardGen_image_last_eq_last_halfTwist_square_v1 (target a5d61856-8526-4cf8-960c-b185fcf7fd81). It is the exact endpoint lemma adjacentHalfTwistConfig_two in the preserved adjacent proof candidate, used to close the double-twist path at baseOrdered.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
open BraidsLinksMCG TarchaBraids

theorem BraidsLinksMCG.adjacentHalfTwistConfig_two_child_v1 (n : ℕ) :
    TarchaBraids.halfTwistConfig (n + 2) (Fin.last n) 2 =
      BraidsLinksMCG.baseOrdered (n + 2) := by sorry
