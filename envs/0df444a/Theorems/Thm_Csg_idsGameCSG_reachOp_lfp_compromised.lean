-- Prove2me | Theorems.Thm_Csg_idsGameCSG_reachOp_lfp_compromised
-- name    : Csg.idsGameCSG_reachOp_lfp_compromised
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:59:12.46711+00:00
-- url     : https://prove2.me/theorems/c54c9a5f-f63d-4460-83fe-62fdd9e5be2a
-- title:
--   Csg: ids Game CSG reach Op lfp compromised
-- statement:
--   The number the whole exercise was after: starting from `compromised`, the defender guarantees
--       eventually returning to `healthy` with probability exactly `1`, regardless of the attacker --
--       the plain-reachability fact behind the informal "visits `healthy` infinitely often" intuition
--       this file's docstring is explicit about *not* formalising.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L252-L255
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L252-L255

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
set_option autoImplicit true
open Csg

theorem Csg.idsGameCSG_reachOp_lfp_compromised :
    ((idsGameCSG.reachOp idsGoalHealthy idsGameCSG_r_zero).lfp .compromised : ℝ) = 1 := by sorry
