-- Prove2me | Theorems.Thm_Csg_idsVStar_fixed
-- name    : Csg.idsVStar_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:12:41.391453+00:00
-- url     : https://prove2.me/theorems/823905ab-da2d-4560-abe1-d09a58a44efd
-- title:
--   Csg: ids VStar fixed
-- statement:
--   **The payoff, part 1.** `idsVStar` is an exact fixed point of `reachOp`. `healthy` closes by
--       `rfl` alone, exactly as `RockPaperScissorsLfp.lean`'s `win2` case does -- no stage game
--       involved, just the structural `ite` on a concrete, decidable state comparison. `compromised`'s
--       stage game against the *constant* continuation `1` has every entry equal to `1` regardless of
--       the joint action (no strategic argument needed for this direction, unlike part 2 below: a
--       `PMF`'s probabilities always sum to `1`), so its value is `1` by squeezing the payoff matrix
--       between the same constant from both directions.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L187-L210
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L187-L210

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
set_option autoImplicit true
open Csg

theorem Csg.idsVStar_fixed :
    idsGameCSG.reachOp idsGoalHealthy idsGameCSG_r_zero idsVStar = idsVStar := by sorry
