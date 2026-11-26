-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tendsto_stretchedHeightShellAllowance_atTop
-- name    : FirstPassageLinearTransport.tendsto_stretchedHeightShellAllowance_atTop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:34:26.3561+00:00
-- url     : https://prove2.me/theorems/00d126c5-5b48-52fb-b8aa-d9d94a1fcc90
-- title:
--   First Passage Linear Transport: tendsto stretched Height Shell Allowance at Top
-- statement:
--   The First Passage Linear Transport construction uses the tendsto stretched Height Shell Allowance at Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L475-L490
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L475-L490

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.tendsto_stretchedHeightShellAllowance_atTop
    {zeta alpha : ℝ} (hzeta : 0 < zeta) (halpha : 0 < alpha) :
    Tendsto (stretchedHeightShellAllowance zeta alpha) atTop atTop := by sorry
