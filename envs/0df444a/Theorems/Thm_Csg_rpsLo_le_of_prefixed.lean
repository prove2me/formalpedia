-- Prove2me | Theorems.Thm_Csg_rpsLo_le_of_prefixed
-- name    : Csg.rpsLo_le_of_prefixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:11:34.408573+00:00
-- url     : https://prove2.me/theorems/e80221e6-a232-4f25-be34-f243943083b6
-- title:
--   Csg: rps Lo le of prefixed
-- statement:
--   **The payoff, lower half.** `rpsLo` lower-bounds every pre-fixed point `b` of `reachOp` --
--       `win2` forces `b win2 ≥ 1` directly from the pre-fixed-point hypothesis, `win1` is free from
--       `[0, 1]`-membership, and `initial`'s own inequality (using only `b win1 ≥ 0`, `b win2 ≥ 1`,
--       `b draw ≥ 0`, all free) already forces `b initial ≥ 1/3`; `draw`'s inequality then chains
--       through that to force `b draw ≥ 1/3` too. Substantively the same argument
--       `RockPaperScissorsLfp.lean`'s `rpsVStar_le_of_prefixed` makes, re-run against the looser
--       target `1/3` rather than `1/2`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsInterval.lean#L85-L111
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsInterval.lean#L85-L111

import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsInterval
set_option autoImplicit true
open Csg

theorem Csg.rpsLo_le_of_prefixed {b : RPSState → Set.Icc (0 : ℝ) 1}
    (hb : rpsCSG.reachOp rpsGoalWin2 rpsR_zero b ≤ b) : rpsLo ≤ b := by sorry
