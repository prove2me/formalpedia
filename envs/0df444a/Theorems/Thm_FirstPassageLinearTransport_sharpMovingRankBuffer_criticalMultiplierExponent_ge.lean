-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_sharpMovingRankBuffer_criticalMultiplierExponent_ge
-- name    : FirstPassageLinearTransport.sharpMovingRankBuffer_criticalMultiplierExponent_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:51:50.300611+00:00
-- url     : https://prove2.me/theorems/b9992f68-4996-5ec2-a1ea-4a472da3a3f2
-- title:
--   First Passage Linear Transport: sharp Moving Rank Buffer critical Multiplier Exponent ge
-- statement:
--   The critical multiplier pays the sharp buffer directly.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L169-L195
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L169-L195

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.sharpMovingRankBuffer_criticalMultiplierExponent_ge
    {U : ℕ → ℝ} (hU : ∀ n, 0 < U n) (M : ℕ) :
    firstPassageEntropyGap *
        Real.logb 2 (clippedCriticalMultiplier U M) ≤
      sharpMovingRankBuffer (criticalMultiplierExponent U) M := by sorry
