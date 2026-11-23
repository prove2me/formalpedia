-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachBounded_initial_four
-- name    : Csg.rpsCSG_reachBounded_initial_four
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:34:14.766279+00:00
-- url     : https://prove2.me/theorems/94d778bc-0d30-4d51-a289-a03497555c65
-- title:
--   Csg: rps CSG reach Bounded initial four
-- statement:
--   `x_4 = 4/9`, same as `x_3` -- the same pairing-up pattern as `x_1 = x_2`, matching the
--       doubled-step-per-round structure `draw` (as its own genuine state) imposes. The sequence
--       `0, 1/3, 1/3, 4/9, 4/9, ...` is exactly the naive one-step-per-round recursion
--       `x_{n+1} = 1/3 + x_n/3` (limit `1/2`), each value now appearing twice.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L344-L347
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L344-L347

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachBounded_initial_four :
    rpsCSG.reachBounded rpsGoalWin2 4 .initial = 4 / 9 := by sorry
