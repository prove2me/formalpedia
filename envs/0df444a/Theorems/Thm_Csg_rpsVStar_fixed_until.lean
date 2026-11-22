-- Prove2me | Theorems.Thm_Csg_rpsVStar_fixed_until
-- name    : Csg.rpsVStar_fixed_until
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:09:41.732945+00:00
-- url     : https://prove2.me/theorems/d17bfb15-8ee2-4ed1-bc66-d27268211b3c
-- title:
--   Csg: rps VStar fixed until
-- statement:
--   **The payoff, part 1.** `rpsVStar` -- the *same* candidate `RockPaperScissorsLfp.lean` used for
--       plain reachability -- is also an exact fixed point of the genuine `until` operator. `win1` and
--       `win2` both close by `rfl` alone now: `win1` is neither `goal` nor `safe`, so `untilOpFun` pins
--       it to `0` directly (no self-loop reasoning needed, unlike the reachability version); `win2` is
--       `goal`, pinned to `1` as before. `initial`/`draw` play the *same* stage game as the reachability
--       version (their `safe`/`goal` status routes to the same stage-value branch either way), so their
--       proofs carry over unchanged.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsUntil.lean#L62-L78
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsUntil.lean#L62-L78

import Definitions.Def_Csg_UntilOp
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsUntil
set_option autoImplicit true
open Csg

theorem Csg.rpsVStar_fixed_until :
    rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero rpsVStar = rpsVStar := by sorry
