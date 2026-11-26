-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingHighDensityProfile_le_rpow
-- name    : FirstPassageLinearTransport.shrinkingHighDensityProfile_le_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:21:35.298293+00:00
-- url     : https://prove2.me/theorems/979580db-7bd4-52b2-a618-bcaf08378156
-- title:
--   First Passage Linear Transport: shrinking High Density Profile le rpow
-- statement:
--   The high-rank profile is a fixed negative power.  The slower of the
--   switch-boundary and quadratic-barrier rates is retained explicitly.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTailAsymptotics.lean#L117-L165
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingTailAsymptotics.lean#L117-L165

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_TerminalTailAsymptotics
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTailAsymptotics
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shrinkingHighDensityProfile_le_rpow
    (P : ShrinkingBarrierRunData) (C : ℝ) (M : ℕ) :
    shrinkingHighDensityProfile P C M ≤
      (1 + quadraticWindowShellConstant) *
        (((M : ℝ) + 2) ^
          (-min (C * Real.log 2) (maximalBarrierC0 * P.D ^ 2))) := by sorry
