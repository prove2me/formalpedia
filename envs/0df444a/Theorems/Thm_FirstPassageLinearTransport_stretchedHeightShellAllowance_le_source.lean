-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stretchedHeightShellAllowance_le_source
-- name    : FirstPassageLinearTransport.stretchedHeightShellAllowance_le_source
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:34:30.069242+00:00
-- url     : https://prove2.me/theorems/a7410d9a-a63d-570a-bbbd-9f8e7fcedfa1
-- title:
--   First Passage Linear Transport: stretched Height Shell Allowance le source
-- statement:
--   The First Passage Linear Transport construction uses the stretched Height Shell Allowance le source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L669-L687
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L669-L687

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.stretchedHeightShellAllowance_le_source
    {zeta alpha : ℝ} (hzeta : 0 ≤ zeta) (halpha : 0 ≤ alpha)
    {M n : ℕ} (hn : n ∈ dyadicShell M) :
    stretchedHeightShellAllowance zeta alpha M ≤
      Real.exp (zeta * (Real.log n) ^ alpha) := by sorry
