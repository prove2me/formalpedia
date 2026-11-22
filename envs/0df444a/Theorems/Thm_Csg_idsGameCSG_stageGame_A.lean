-- Prove2me | Theorems.Thm_Csg_idsGameCSG_stageGame_A
-- name    : Csg.idsGameCSG_stageGame_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:52:28.379182+00:00
-- url     : https://prove2.me/theorems/35d6fca2-5e3b-4a6a-8025-06b2e4f5a838
-- title:
--   Csg: ids Game CSG stage Game A
-- statement:
--   `idsGameCSG`'s stage-game payoff matrix against an arbitrary continuation `v`: identical in
--       shape to `IntrusionDetection.lean`'s `idsCSG_stageGame_A'`, but without the reward term (`r`
--       is identically `0` here), so it is exactly `v` evaluated at the deterministic next state.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L81-L88
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/IntrusionDetectionReach.lean#L81-L88

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
set_option autoImplicit true
open Csg

theorem Csg.idsGameCSG_stageGame_A (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction)
    (v : IDSState → ℝ) :
    (idsGameCSG.stageGame s v).A a1 a2 = v (idsNext a1 a2) := by sorry
