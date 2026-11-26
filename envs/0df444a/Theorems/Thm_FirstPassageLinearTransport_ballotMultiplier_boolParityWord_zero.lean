-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ballotMultiplier_boolParityWord_zero
-- name    : FirstPassageLinearTransport.ballotMultiplier_boolParityWord_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:29:04.671978+00:00
-- url     : https://prove2.me/theorems/f1facb10-f9a2-4403-ba65-1f54ff133177
-- title:
--   First Passage Linear Transport: ballot Multiplier bool Parity Word zero
-- statement:
--   The First Passage Linear Transport construction uses the ballot Multiplier bool Parity Word zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L40-L43
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/OrbitCeiling.lean#L40-L43

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.ballotMultiplier_boolParityWord_zero (r n : ℕ) :
    ballotMultiplier (boolParityWord (r + 1) n 0) =
      (3 : ℝ) ^ (parityBit n 0 : ℕ) / 2 := by sorry
