-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellBad_heightCertifiedShell_subset
-- name    : FirstPassageLinearTransport.shellBad_heightCertifiedShell_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:04.231513+00:00
-- url     : https://prove2.me/theorems/52e2a8d0-c004-4f9c-b0f9-24118730d24c
-- title:
--   First Passage Linear Transport: shell Bad height Certified Shell subset
-- statement:
--   The First Passage Linear Transport construction uses the shell Bad height Certified Shell subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L234-L249
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L234-L249

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shellBad_heightCertifiedShell_subset
    {r eta omega zeta alpha : ℝ} (p : StageSetup r eta) (M : ℕ) :
    shellBad (heightCertifiedShell p omega zeta alpha M) M ⊆
      shellBad (shellBootstrap p omega M) M ∪
        shellMultiplicativeHit M
          (stretchedHeightShellAllowance zeta alpha M / 4) := by sorry
