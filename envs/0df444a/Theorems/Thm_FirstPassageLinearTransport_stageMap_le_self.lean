-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageMap_le_self
-- name    : FirstPassageLinearTransport.stageMap_le_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:56:46.570066+00:00
-- url     : https://prove2.me/theorems/b9d15c08-0c63-4d23-90e5-12dd19d6843c
-- title:
--   First Passage Linear Transport: stage Map le self
-- statement:
--   A stopped block never increases its checkpoint.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L32-L43
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L32-L43

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.stageMap_le_self
    {r eta : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p) :
    stageMap p n ≤ n := by sorry
