-- Prove2me | Theorems.Thm_Csg_rpsCSG_stageValue_initial
-- name    : Csg.rpsCSG_stageValue_initial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:43:13.196366+00:00
-- url     : https://prove2.me/theorems/34ae5a9f-98bb-4090-a560-d26bba023b68
-- title:
--   Csg: rps CSG stage Value initial
-- statement:
--   **The payoff.** `initial`'s stage-game value, for *any* continuation `v`: the average of `v` at
--       the three possible outcomes. Same `value_unique` + uniform-strategy-is-a-saddle-point argument
--       `MatchingPennies.lean` used, generalised from two actions to three.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L246-L261
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L246-L261

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_stageValue_initial (v : RPSState → ℝ) :
    rpsCSG.stageValue .initial v = (v .win1 + v .win2 + v .draw) / 3 := by sorry
