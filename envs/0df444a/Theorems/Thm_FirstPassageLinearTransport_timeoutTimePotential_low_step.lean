-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutTimePotential_low_step
-- name    : FirstPassageLinearTransport.timeoutTimePotential_low_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:42.436868+00:00
-- url     : https://prove2.me/theorems/521eef2e-717c-5509-b3f9-923401493e48
-- title:
--   First Passage Linear Transport: timeout Time Potential low step
-- statement:
--   One timeout block pays its whole crude corridor by strict rank descent.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L276-L305
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L276-L305

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutTimePotential_low_step
    (P : TimeoutHighRunData) {K₀ : ℝ} {L M S qPrev m x : ℕ}
    (hmS : m < S) (hpass : LowTimeoutPassage K₀ L m x)
    (hmPrevLo : m ≤ qPrev) (hmPrevHi : qPrev ≤ m + 1)
    (hqparent : timeoutTargetRank K₀ L m < m) :
    (|driftGap * (hpass.duration : ℝ) -
        ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1) +
        timeoutTimePotential P M S (timeoutTargetRank K₀ L m) ≤
      timeoutTimePotential P M S qPrev := by sorry
