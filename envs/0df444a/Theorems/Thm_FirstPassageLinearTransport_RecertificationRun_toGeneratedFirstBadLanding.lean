-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_toGeneratedFirstBadLanding
-- name    : FirstPassageLinearTransport.RecertificationRun.toGeneratedFirstBadLanding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:43:46.531909+00:00
-- url     : https://prove2.me/theorems/f177be34-2ef8-5aab-b2ea-68d8cadfbc38
-- title:
--   Recertification Run: to Generated First Bad Landing
-- statement:
--   A failed endpoint of a complete certified run supplies the exact generated
--   first-bad witness consumed by `generatedFirstBadSources_subset_envelope`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationRun.lean#L115-L123
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationRun.lean#L115-L123

import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.RecertificationRun.toGeneratedFirstBadLanding
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta}
    {n elapsed q L U H : ℕ}
    (hrun : RecertificationRun p n elapsed q)
    (hLq : L ≤ q) (hqU : q ≤ U) (hhH : elapsed ≤ H)
    (hbad : orbit elapsed n ∉ initialWindowGood eta) :
    HasGeneratedFirstBadLanding r eta n L U H := by sorry
