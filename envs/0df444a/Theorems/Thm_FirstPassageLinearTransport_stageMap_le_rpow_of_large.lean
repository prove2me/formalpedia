-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageMap_le_rpow_of_large
-- name    : FirstPassageLinearTransport.stageMap_le_rpow_of_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:39.913465+00:00
-- url     : https://prove2.me/theorems/ac2a9edc-0959-52ac-85a3-a9e3829dc0cb
-- title:
--   First Passage Linear Transport: stage Map le rpow of large
-- statement:
--   On the large branch, the first stopped checkpoint pays no startup
--   constant: it lies below the exact power of its source.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L47-L75
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/StretchedRelativeHeight.lean#L47-L75

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.stageMap_le_rpow_of_large
    {r eta : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p)
    (hlarge : p.M0 ≤ Nat.log 2 n) :
    (stageMap p n : ℝ) ≤ (n : ℝ) ^ r := by sorry
