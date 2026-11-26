-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_le_one_add_eta_of_le_stageLength
-- name    : FirstPassageLinearTransport.orbit_le_one_add_eta_of_le_stageLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:19:50.617455+00:00
-- url     : https://prove2.me/theorems/3088db2e-c71b-4e26-b4f7-c75591c5ad54
-- title:
--   First Passage Linear Transport: orbit le one add eta of le stage Length
-- statement:
--   Every prefix of one retained stopped block stays below the local
--   `1 + eta` power envelope.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L374-L400
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L374-L400

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.orbit_le_one_add_eta_of_le_stageLength
    {r eta : ℝ} (p : StageSetup r eta) {n j : ℕ}
    (hn : 0 < n) (hnW : n ∈ extendedWindow p)
    (hj : j ≤ stageLength p n) :
    (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + eta) := by sorry
