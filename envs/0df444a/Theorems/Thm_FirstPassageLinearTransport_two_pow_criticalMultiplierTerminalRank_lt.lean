-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_two_pow_criticalMultiplierTerminalRank_lt
-- name    : FirstPassageLinearTransport.two_pow_criticalMultiplierTerminalRank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:53:20.607584+00:00
-- url     : https://prove2.me/theorems/ec587ea8-3aff-46a9-a5bf-83ed2cb26d01
-- title:
--   First Passage Linear Transport: two pow critical Multiplier Terminal Rank lt
-- statement:
--   The chosen integer scale is at most one factor two above the critical
--   rank times the clipped multiplier.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L340-L380
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L340-L380

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.two_pow_criticalMultiplierTerminalRank_lt
    {U : ℕ → ℝ} (hUpos : ∀ n, 0 < U n) {M : ℕ}
    (hw1 : 1 ≤ clippedCriticalMultiplier U M) :
    (2 : ℝ) ^ (criticalMultiplierTerminalRank U M) <
      2 * (((M : ℝ) + 2) ^ timeSupportCriticalExponent) *
        clippedCriticalMultiplier U M := by sorry
