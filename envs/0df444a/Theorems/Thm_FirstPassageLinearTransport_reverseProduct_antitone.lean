-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseProduct_antitone
-- name    : FirstPassageLinearTransport.reverseProduct_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:39.636532+00:00
-- url     : https://prove2.me/theorems/5cf54ab0-99e4-4e39-b7bc-853f8f197064
-- title:
--   First Passage Linear Transport: reverse Product antitone
-- statement:
--   Reverse products can only decrease when a shortcut prefix is extended.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L692-L710
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L692-L710

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.reverseProduct_antitone
    {n a b : ℕ} (hn : 0 < n) (hab : a ≤ b) :
    reverseProduct n b ≤ reverseProduct n a := by sorry
