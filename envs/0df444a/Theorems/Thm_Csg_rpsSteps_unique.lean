-- Prove2me | Theorems.Thm_Csg_rpsSteps_unique
-- name    : Csg.rpsSteps_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:21:13.287387+00:00
-- url     : https://prove2.me/theorems/50cbae16-c042-4fb2-95de-fc5222e5fdf4
-- title:
--   Csg: rps Steps unique
-- statement:
--   **The payoff, part 2, and the reason working in plain `ℝ` was worth it.** `rpsSteps` is the
--       *unique* real-valued fixed point of `rpsStepsStep` -- not merely a lower bound over pre-fixed
--       points the way `RockPaperScissorsLfp.lean`'s Knaster-Tarski certificate had to settle for.
--       `win1`/`win2` are forced to `0` for *any* fixed point `w` by `rpsStepsStep`'s own absorbing
--       branch (`change` again does the defeq work); the remaining two equations, once those zeros are
--       substituted in, are a genuine invertible linear system in `w initial`/`w draw` with exactly one
--       real solution, closed by `linarith` alone -- no completeness-of-`[0,1]` argument, no `sSup`, no
--       interval sandwiching, just linear algebra.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L224-L250
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsSteps.lean#L224-L250

import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RewardUntilCertificate
import Definitions.Def_Csg_RockPaperScissorsSteps
set_option autoImplicit true
open Csg

theorem Csg.rpsSteps_unique {w : RPSState → ℝ} (hw : rpsStepsStep w = w) : w = rpsSteps := by sorry
