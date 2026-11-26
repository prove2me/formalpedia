-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_bootstrapLogBoundScheduleLe
-- name    : FirstPassageLinearTransport.bootstrapLogBoundScheduleLe
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:28:40.04375+00:00
-- url     : https://prove2.me/theorems/199963e4-e24b-4902-a506-f50e7489a81e
-- title:
--   First Passage Linear Transport: bootstrap Log Bound Schedule Le
-- statement:
--   On a logarithmic schedule, the full recursively generated prefactor has
--   only quadratic-logarithmic cost.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BootstrapSchedule.lean#L134-L209
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BootstrapSchedule.lean#L134-L209

import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section

theorem FirstPassageLinearTransport.bootstrapLogBoundScheduleLe
    {r eta chi Dc omega : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (homega0 : 0 ≤ omega) (M : ℕ) :
    bootstrapLogBound p chi Dc (stageCount omega M) ≤
      bootstrapScheduleA p chi Dc omega *
        (Real.log ((M : ℝ) + 4) + 1) ^ 2 := by sorry
