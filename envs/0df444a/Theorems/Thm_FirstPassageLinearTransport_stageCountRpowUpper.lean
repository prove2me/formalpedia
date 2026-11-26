-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageCountRpowUpper
-- name    : FirstPassageLinearTransport.stageCountRpowUpper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:44:36.200898+00:00
-- url     : https://prove2.me/theorems/2254d195-d0c1-509a-a638-1ab0b329f614
-- title:
--   First Passage Linear Transport: stage Count Rpow Upper
-- statement:
--   Flooring the logarithmic stage count costs at most one factor of `r⁻¹`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedLogLanding.lean#L97-L115
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedLogLanding.lean#L97-L115

import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
import Definitions.Def_FirstPassageLinearTransport_StretchedLogLanding
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section

theorem FirstPassageLinearTransport.stageCountRpowUpper
    {r omega : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (M : ℕ) :
    r ^ (stageCount omega M) ≤
      r⁻¹ * ((M : ℝ) + 4) ^ (-descentAlpha omega r) := by sorry
