-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellExceptionalRatio_heightCertifiedShell_le
-- name    : FirstPassageLinearTransport.shellExceptionalRatio_heightCertifiedShell_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:57:06.27881+00:00
-- url     : https://prove2.me/theorems/2e76c581-2dc8-451e-a660-94f38ba9a06f
-- title:
--   First Passage Linear Transport: shell Exceptional Ratio height Certified Shell le
-- statement:
--   Removing the multiplicative-hit event adds only its exact reciprocal
--   shell cost to the bootstrap exceptional ratio.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L253-L287
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L253-L287

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shellExceptionalRatio_heightCertifiedShell_le
    {r eta omega zeta alpha : ℝ} (p : StageSetup r eta) (M : ℕ) :
    shellExceptionalRatio (heightCertifiedShell p omega zeta alpha M) M ≤
      shellExceptionalRatio (shellBootstrap p omega M) M +
        ((shellMultiplicativeHit M
          (stretchedHeightShellAllowance zeta alpha M / 4)).card : ℝ) /
            (2 : ℝ) ^ M := by sorry
