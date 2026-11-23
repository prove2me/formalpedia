-- Prove2me | Theorems.Thm_Csg_rpsVStarSafety_upper_bound
-- name    : Csg.rpsVStarSafety_upper_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:11:15.382782+00:00
-- url     : https://prove2.me/theorems/0631b483-49a5-49c8-b66e-4b2f5ff7d70f
-- title:
--   Csg: rps VStar Safety upper bound
-- statement:
--   **The payoff, part 2.** `rpsVStarSafety` upper-bounds every post-fixed point `b` of
--       `safetyOp` -- `win1`/`win2` are forced to exactly `0` first (sandwiched between the ambient
--       `[0, 1]`-membership lower bound and the absorption branch's `0` upper bound), then `draw`'s and
--       `initial`'s own post-fixed-point inequalities chain via `linarith` to force `b draw = 0` and
--       hence `b initial = 0` too. The dual, in shape, of `rpsVStar_le_of_prefixed`'s own case split.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSafety.lean#L107-L137
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSafety.lean#L107-L137

import Definitions.Def_Csg_SafetyCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsSafety
set_option autoImplicit true
open Csg

theorem Csg.rpsVStarSafety_upper_bound {b : RPSState → Set.Icc (0 : ℝ) 1}
    (hb : b ≤ rpsCSG.safetyOp rpsSafeUnresolved rpsR_zero b) : b ≤ rpsVStarSafety := by sorry
