-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_tendsto_sqrt_dyadicShellMinimum_atTop
-- name    : FirstPassageLinearTransport.tendsto_sqrt_dyadicShellMinimum_atTop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:32:55.284907+00:00
-- url     : https://prove2.me/theorems/c496eb3e-1e9f-5bad-9b75-80ea5335beec
-- title:
--   First Passage Linear Transport: tendsto sqrt dyadic Shell Minimum at Top
-- statement:
--   The First Passage Linear Transport construction uses the tendsto sqrt dyadic Shell Minimum at Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L90-L105
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/CriticalEndpointConsequences.lean#L90-L105

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.tendsto_sqrt_dyadicShellMinimum_atTop
    {U : ℕ → ℝ} (hU : Tendsto U atTop atTop) :
    Tendsto (fun M => Real.sqrt (dyadicShellMinimum U M)) atTop atTop := by sorry
