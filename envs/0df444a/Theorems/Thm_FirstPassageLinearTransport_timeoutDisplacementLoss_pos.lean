-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutDisplacementLoss_pos
-- name    : FirstPassageLinearTransport.timeoutDisplacementLoss_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:40:53.127381+00:00
-- url     : https://prove2.me/theorems/577dfc3b-e79b-409b-ae4f-0414d84dd99f
-- title:
--   First Passage Linear Transport: timeout Displacement Loss pos
-- statement:
--   The First Passage Linear Transport construction uses the timeout Displacement Loss pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L569-L575
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L569-L575

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeoutDisplacementLoss_pos {K₀ : ℝ} (hK₀ : 0 ≤ K₀) :
    0 < timeoutDisplacementLoss K₀ := by sorry
