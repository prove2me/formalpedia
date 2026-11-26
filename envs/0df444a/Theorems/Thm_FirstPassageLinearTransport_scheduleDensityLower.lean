-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_scheduleDensityLower
-- name    : FirstPassageLinearTransport.scheduleDensityLower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:28:37.824122+00:00
-- url     : https://prove2.me/theorems/d21cd2c2-117c-484b-a9b8-f638ff5c9b54
-- title:
--   First Passage Linear Transport: schedule Density Lower
-- statement:
--   Flooring the logarithmic stage count can only improve the terminal
--   density exponent, because `chi ≤ 1`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BootstrapSchedule.lean#L110-L122
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/BootstrapSchedule.lean#L110-L122

import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
import Definitions.Def_FirstPassageLinearTransport_BootstrapSchedule
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
open Filter
noncomputable section

theorem FirstPassageLinearTransport.scheduleDensityLower
    {chi Dc omega : ℝ} (hchi0 : 0 < chi) (hchi1 : chi ≤ 1)
    (hDc0 : 0 ≤ Dc) (homega0 : 0 ≤ omega) (M : ℕ) :
    Dc * ((M : ℝ) + 4) ^ (-densityGamma omega chi) ≤
      bootstrapD chi Dc (stageCount omega M) := by sorry
