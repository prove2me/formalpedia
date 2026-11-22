-- Prove2me | Theorems.Thm_Csg_idsVStar_le_of_prefixed
-- name    : Csg.idsVStar_le_of_prefixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:12:41.473727+00:00
-- url     : https://prove2.me/theorems/13bc1bbd-fcff-4d5b-ad82-573fe848b571
-- title:
--   Csg: ids VStar le of prefixed
-- statement:
--   **The payoff, part 2.** `idsVStar` lower-bounds every pre-fixed point `b` of `reachOp`:
--       `b healthy = 1` is forced by goal absorption (sandwiched between the pre-fixed-point inequality
--       and `[0, 1]` membership, exactly `RockPaperScissorsLfp.lean`'s `hwin2`), and
--       `idsGameCSG_compromised_stageValue` turns `compromised`'s own pre-fixed-point inequality into
--       `(1 + b compromised) / 2 ≤ b compromised`, forcing `b compromised ≥ 1`. This is the one part of
--       the argument doing genuine work -- the uniform-strategy computation is what makes the average
--       formula exact rather than a mere bound.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L219-L238
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L219-L238

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
set_option autoImplicit true
open Csg

theorem Csg.idsVStar_le_of_prefixed {b : IDSState → Set.Icc (0 : ℝ) 1}
    (hb : idsGameCSG.reachOp idsGoalHealthy idsGameCSG_r_zero b ≤ b) : idsVStar ≤ b := by sorry
