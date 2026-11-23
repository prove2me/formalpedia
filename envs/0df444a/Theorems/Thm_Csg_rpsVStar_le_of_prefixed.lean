-- Prove2me | Theorems.Thm_Csg_rpsVStar_le_of_prefixed
-- name    : Csg.rpsVStar_le_of_prefixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:09:40.410868+00:00
-- url     : https://prove2.me/theorems/1bb58e38-79c7-41a4-a273-3005df3cae26
-- title:
--   Csg: rps VStar le of prefixed
-- statement:
--   **The payoff, part 2.** `rpsVStar` lower-bounds every pre-fixed point `b` of `reachOp`, forcing
--       `b win2 = 1` and `b win1 ≥ 0` first, then chaining `draw`'s and `initial`'s own pre-fixed-point
--       inequalities via `linarith` to pin `b initial ≥ 1/2` (and hence `b draw ≥ 1/2` too). This is
--       the one part of the argument that is genuinely rock-paper-scissors-specific, not reusable
--       as-is (see the module docstring).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsLfp.lean#L116-L144
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsLfp.lean#L116-L144

import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RockPaperScissorsLfp
set_option autoImplicit true
open Csg

theorem Csg.rpsVStar_le_of_prefixed {b : RPSState → Set.Icc (0 : ℝ) 1}
    (hb : rpsCSG.reachOp rpsGoalWin2 rpsR_zero b ≤ b) : rpsVStar ≤ b := by sorry
