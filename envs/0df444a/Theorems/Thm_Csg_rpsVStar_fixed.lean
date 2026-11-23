-- Prove2me | Theorems.Thm_Csg_rpsVStar_fixed
-- name    : Csg.rpsVStar_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:09:31.451962+00:00
-- url     : https://prove2.me/theorems/0df7d498-e547-4590-8bc0-26dc325131c5
-- title:
--   Csg: rps VStar fixed
-- statement:
--   **The payoff, part 1.** `rpsVStar` is an exact fixed point of `reachOp`: a per-state case
--       split. `win2` closes by `rfl` alone -- no stage game involved, just a purely structural `ite`
--       on a concrete state comparison. The other three `change` the goal past the `OrderHom`/`ite`
--       packaging directly to a bare `stageValue` equation (a defeq jump the elaborator can make in
--       one step, since the condition is a concrete, decidable comparison between two `RPSState`
--       constructors) and close with `RockPaperScissors.lean`'s own stage-value lemmas plus
--       arithmetic.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsLfp.lean#L90-L109
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsLfp.lean#L90-L109

import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RockPaperScissorsLfp
set_option autoImplicit true
open Csg

theorem Csg.rpsVStar_fixed :
    rpsCSG.reachOp rpsGoalWin2 rpsR_zero rpsVStar = rpsVStar := by sorry
