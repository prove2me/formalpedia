-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_endpoint_mem_landingBad
-- name    : FirstPassageLinearTransport.RecertificationRun.endpoint_mem_landingBad
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:16:17.64542+00:00
-- url     : https://prove2.me/theorems/c601c44a-de03-54c6-a66d-4dc0d879a86b
-- title:
--   Recertification Run: endpoint mem landing Bad
-- statement:
--   If the endpoint of a certified run is not certified, it belongs to the
--   exact first-bad landing band at the run's final threshold rank.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationRun.lean#L98-L111
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RecertificationRun.lean#L98-L111

import Definitions.Def_FirstPassageLinearTransport_RecertificationStep
import Definitions.Def_FirstPassageLinearTransport_RecertificationRun
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.RecertificationRun.endpoint_mem_landingBad
    {r : ℚ} {eta : ℝ} {p : StageSetup (r : ℝ) eta} {n elapsed q : ℕ}
    (hrun : RecertificationRun p n elapsed q)
    (hbad : orbit elapsed n ∉ initialWindowGood eta) :
    orbit elapsed n ∈ landingBad q eta := by sorry
