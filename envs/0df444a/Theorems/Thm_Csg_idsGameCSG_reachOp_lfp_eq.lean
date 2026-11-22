-- Prove2me | Theorems.Thm_Csg_idsGameCSG_reachOp_lfp_eq
-- name    : Csg.idsGameCSG_reachOp_lfp_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:12:45.645111+00:00
-- url     : https://prove2.me/theorems/3ccde087-3910-4753-9eab-09b1b9132aae
-- title:
--   Csg: ids Game CSG reach Op lfp eq
-- statement:
--   **The headline result.** `idsVStar` (the constant `1`) *is* the least fixed point of `reachOp`
--       for reaching `healthy`, on the nose -- no limiting argument, the two payoff lemmas above fed
--       into `ReachCertificate.lean`'s reusable `CSG.reachOp_lfp_eq_of_certificate`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L243-L246
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L243-L246

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
set_option autoImplicit true
open Csg

theorem Csg.idsGameCSG_reachOp_lfp_eq :
    (idsGameCSG.reachOp idsGoalHealthy idsGameCSG_r_zero).lfp = idsVStar := by sorry
