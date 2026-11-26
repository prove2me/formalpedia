-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ballotMultiplier_finTwoEquiv
-- name    : FirstPassageLinearTransport.ballotMultiplier_finTwoEquiv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:45:34.644618+00:00
-- url     : https://prove2.me/theorems/c4939b8f-2fb2-401a-8310-bbe8d82d6214
-- title:
--   First Passage Linear Transport: ballot Multiplier fin Two Equiv
-- statement:
--   The First Passage Linear Transport construction uses the ballot Multiplier fin Two Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L29-L38
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L29-L38

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.ballotMultiplier_finTwoEquiv (b : Fin 2) :
    ballotMultiplier (finTwoEquiv b) = (3 : ℝ) ^ (b : ℕ) / 2 := by sorry
