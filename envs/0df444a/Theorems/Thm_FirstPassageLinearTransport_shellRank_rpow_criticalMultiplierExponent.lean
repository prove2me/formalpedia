-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellRank_rpow_criticalMultiplierExponent
-- name    : FirstPassageLinearTransport.shellRank_rpow_criticalMultiplierExponent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:53:20.468919+00:00
-- url     : https://prove2.me/theorems/2e19e61d-5b29-4689-b1ba-8aacb338945d
-- title:
--   First Passage Linear Transport: shell Rank rpow critical Multiplier Exponent
-- statement:
--   The exponent representation is exact: raising the shifted shell rank to
--   the induced exponent gives the chosen integer power of two.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L276-L299
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L276-L299

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shellRank_rpow_criticalMultiplierExponent
    (U : ℕ → ℝ) (M : ℕ) :
    (((M : ℝ) + 2) ^ (criticalMultiplierExponent U M)) =
      (2 : ℝ) ^ (criticalMultiplierTerminalRank U M) := by sorry
