-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellExceptionalRatio_heightCertifiedShell_le_inv
-- name    : FirstPassageLinearTransport.shellExceptionalRatio_heightCertifiedShell_le_inv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:34:22.60496+00:00
-- url     : https://prove2.me/theorems/98e96219-5733-58a5-87b9-95c4c52bca62
-- title:
--   First Passage Linear Transport: shell Exceptional Ratio height Certified Shell le inv
-- statement:
--   The First Passage Linear Transport construction uses the shell Exceptional Ratio height Certified Shell le inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L289-L299
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L289-L299

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shellExceptionalRatio_heightCertifiedShell_le_inv
    {r eta omega zeta alpha : ℝ} (p : StageSetup r eta) (M : ℕ) :
    shellExceptionalRatio (heightCertifiedShell p omega zeta alpha M) M ≤
      shellExceptionalRatio (shellBootstrap p omega M) M +
        4 / stretchedHeightShellAllowance zeta alpha M := by sorry
