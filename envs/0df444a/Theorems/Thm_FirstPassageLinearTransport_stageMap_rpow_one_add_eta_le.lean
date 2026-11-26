-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageMap_rpow_one_add_eta_le
-- name    : FirstPassageLinearTransport.stageMap_rpow_one_add_eta_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:45:38.429977+00:00
-- url     : https://prove2.me/theorems/622023e8-857d-5253-bddd-3c62379ac9f2
-- title:
--   First Passage Linear Transport: stage Map rpow one add eta le
-- statement:
--   Raising one stopped endpoint to the local envelope exponent costs at
--   most two powers of the fixed startup constant.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L404-L436
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L404-L436

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.stageMap_rpow_one_add_eta_le
    {r eta : ℝ} (p : StageSetup r eta) {n : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p) :
    (stageMap p n : ℝ) ^ (1 + eta) ≤
      stageK p ^ 2 * (n : ℝ) ^ (1 + eta) := by sorry
