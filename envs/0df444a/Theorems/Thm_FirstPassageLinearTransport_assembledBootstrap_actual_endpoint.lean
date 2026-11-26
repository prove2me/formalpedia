-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_assembledBootstrap_actual_endpoint
-- name    : FirstPassageLinearTransport.assembledBootstrap_actual_endpoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:44:03.586398+00:00
-- url     : https://prove2.me/theorems/b03ebc1d-7be3-5432-9d3b-904641cc15df
-- title:
--   First Passage Linear Transport: assembled Bootstrap actual endpoint
-- statement:
--   The varying-shell endpoint is one literal shortcut iterate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/GlobalAssembly.lean#L41-L45
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/GlobalAssembly.lean#L41-L45

import Definitions.Def_FirstPassageLinearTransport_HeadlineParameters
import Definitions.Def_FirstPassageLinearTransport_GlobalAssembly
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.assembledBootstrap_actual_endpoint
    {r eta : ℝ} (p : StageSetup r eta) {omega : ℝ} {n : ℕ}
    : stageOrbit p (stageCount omega (Nat.log 2 n)) n =
      orbit (stageClock p (stageCount omega (Nat.log 2 n)) n) n := by sorry
