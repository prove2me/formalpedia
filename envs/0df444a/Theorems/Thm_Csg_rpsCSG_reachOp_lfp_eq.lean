-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachOp_lfp_eq
-- name    : Csg.rpsCSG_reachOp_lfp_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:53:17.709647+00:00
-- url     : https://prove2.me/theorems/24fc8f8a-edc2-4c69-b077-193150847828
-- title:
--   Csg: rps CSG reach Op lfp eq
-- statement:
--   **The headline result.** `rpsVStar` *is* the least fixed point, on the nose -- no limiting
--       argument, just the two payoff lemmas above fed into `ReachCertificate.lean`'s reusable
--       `CSG.reachOp_lfp_eq_of_certificate` combinator, rather than an inlined `le_antisymm`. Deriving
--       it through the generic combinator rather than a hand-rolled proof is itself a regression check
--       that the generalisation is real and not cosmetic.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsLfp.lean#L151-L154
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsLfp.lean#L151-L154

import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RockPaperScissorsLfp
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachOp_lfp_eq :
    (rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp = rpsVStar := by sorry
