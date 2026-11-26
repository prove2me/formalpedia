-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellLog_rpow_criticalMultiplierExponent_le
-- name    : FirstPassageLinearTransport.shellLog_rpow_criticalMultiplierExponent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:52:52.336189+00:00
-- url     : https://prove2.me/theorems/d6e9ae11-fbda-54da-921d-4777a61a48c4
-- title:
--   First Passage Linear Transport: shell Log rpow critical Multiplier Exponent le
-- statement:
--   On its source shell, the induced polylogarithmic target is bounded by
--   the selected integer terminal scale.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L303-L336
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L303-L336

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shellLog_rpow_criticalMultiplierExponent_le
    (U : ℕ → ℝ) {M n : ℕ} (hM : 1 ≤ M)
    (hnShell : n ∈ dyadicShell M) :
    (Real.log n) ^ (criticalMultiplierExponent U M) ≤
      (2 : ℝ) ^ (criticalMultiplierTerminalRank U M) := by sorry
