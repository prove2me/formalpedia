-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_movingTerminalRank_criticalMultiplierExponent
-- name    : FirstPassageLinearTransport.movingTerminalRank_criticalMultiplierExponent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:51:44.944618+00:00
-- url     : https://prove2.me/theorems/d22c7098-ce08-5f88-8ef7-1997b75ccbd2
-- title:
--   First Passage Linear Transport: moving Terminal Rank critical Multiplier Exponent
-- statement:
--   The First Passage Linear Transport construction uses the moving Terminal Rank critical Multiplier Exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L146-L156
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L146-L156

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.movingTerminalRank_criticalMultiplierExponent
    (U : ℕ → ℝ) (M : ℕ) :
    movingTerminalRank (criticalMultiplierExponent U) M =
      criticalMultiplierTerminalRank U M := by sorry
