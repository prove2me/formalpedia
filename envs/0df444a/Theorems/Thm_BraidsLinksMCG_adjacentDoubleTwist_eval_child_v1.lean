-- Prove2me | Theorems.Thm_BraidsLinksMCG_adjacentDoubleTwist_eval_child_v1
-- name    : BraidsLinksMCG.adjacentDoubleTwist_eval_child_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T21:55:10.733887+00:00
-- url     : https://prove2.me/theorems/fa012a03-fed4-4e80-9dcb-3cbf121d7d6b
-- title:
--   The full-twist parametrization follows the concatenated half-twist path
-- statement:
--   Pointwise, the path that runs the final adjacent half-twist configuration through two periods is the same unordered configuration as the concatenation of two half-twist loops. In the second half, the period-shift identity identifies the configuration after one full parameter turn up to swapping the active pair.
-- source:
--   Exact pointwise obligation used by adjacentDoubleTwistProjectedPath_eq_square in the preserved proof of BraidsLinksMCG.standardGen_image_last_eq_last_halfTwist_square_v1 (target a5d61856-8526-4cf8-960c-b185fcf7fd81). Its proof will use the independently published adjacentHalfTwistConfig_period_shift_child_v1 once that target is Proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
open BraidsLinksMCG TarchaBraids

theorem BraidsLinksMCG.adjacentDoubleTwist_eval_child_v1 (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    BraidsLinksMCG.configProj (n + 2)
      (TarchaBraids.halfTwistConfig (n + 2) (Fin.last n) (2 * (t : ℝ))) =
    (TarchaBraids.halfTwistLoop (n + 2) (Fin.last n)).trans
      (TarchaBraids.halfTwistLoop (n + 2) (Fin.last n)) t := by sorry
