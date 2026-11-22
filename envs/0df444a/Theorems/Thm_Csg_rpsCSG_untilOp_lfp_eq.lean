-- Prove2me | Theorems.Thm_Csg_rpsCSG_untilOp_lfp_eq
-- name    : Csg.rpsCSG_untilOp_lfp_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:53:31.24813+00:00
-- url     : https://prove2.me/theorems/3d7689bd-9bac-402d-9a52-e2cfc653e554
-- title:
--   Csg: rps CSG until Op lfp eq
-- statement:
--   **The headline result.** The genuine `until` reading of this property has *exactly* the same
--       least fixed point as the plain-reachability reading -- concrete, if RPS-specific, evidence for
--       the general `reachOp goal hr = untilOp (fun _ => True) goal hr` corollary deferred out of
--       `UntilOp.lean` (not that statement itself, since `rpsSafeNotWin1` isn't the always-`True`
--       predicate that corollary needs, but the same underlying phenomenon: a safety clause that turns
--       out to cost nothing on this particular game).
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsUntil.lean#L124-L127
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsUntil.lean#L124-L127

import Definitions.Def_Csg_UntilOp
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsUntil
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_untilOp_lfp_eq :
    (rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero).lfp = rpsVStar := by sorry
