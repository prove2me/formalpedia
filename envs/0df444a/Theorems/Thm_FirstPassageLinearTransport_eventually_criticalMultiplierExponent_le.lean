-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_criticalMultiplierExponent_le
-- name    : FirstPassageLinearTransport.eventually_criticalMultiplierExponent_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:52:07.799224+00:00
-- url     : https://prove2.me/theorems/4d1756e4-f7bd-4452-b844-f02cb28a255c
-- title:
--   First Passage Linear Transport: eventually critical Multiplier Exponent le
-- statement:
--   The clipped multiplier induces an eventually bounded exponent sequence.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L217-L263
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L217-L263

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.eventually_criticalMultiplierExponent_le
    {U : ℕ → ℝ} (hU : Tendsto U atTop atTop) :
    ∀ᶠ M : ℕ in atTop,
      criticalMultiplierExponent U M < timeSupportCriticalExponent + 2 := by sorry
