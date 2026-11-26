-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_weightedSurvivalWordMass_half_eq_card
-- name    : FirstPassageLinearTransport.weightedSurvivalWordMass_half_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:27.353801+00:00
-- url     : https://prove2.me/theorems/456dd42f-f872-56d9-872d-cd4d494cd08a
-- title:
--   First Passage Linear Transport: weighted Survival Word Mass half eq card
-- statement:
--   At fair weight, normalized survivor cardinality is exactly survivor
--   mass.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L342-L361
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutDensity.lean#L342-L361

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.weightedSurvivalWordMass_half_eq_card
    (m : ℕ) (B : ℝ) :
    weightedSurvivalWordMass (1 / 2) collatzLogIncrement (-B) m 0 =
      ((collatzSurvivalWords m B).card : ℝ) / (2 : ℝ) ^ m := by sorry
