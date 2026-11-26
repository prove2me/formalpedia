-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_weightedSurvivalWordMass_eq_lowerSurvivalMass
-- name    : FirstPassageLinearTransport.weightedSurvivalWordMass_eq_lowerSurvivalMass
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:34:46.879076+00:00
-- url     : https://prove2.me/theorems/99f7a536-936c-424e-acec-cb61064334ad
-- title:
--   First Passage Linear Transport: weighted Survival Word Mass eq lower Survival Mass
-- statement:
--   The First Passage Linear Transport construction uses the weighted Survival Word Mass eq lower Survival Mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1592-L1608
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1592-L1608

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.weightedSurvivalWordMass_eq_lowerSurvivalMass
    (p : ℝ) (x : Bool → ℝ) (lo : ℝ) :
    ∀ r z, weightedSurvivalWordMass p x lo r z =
      lowerSurvivalMass p x lo r z := by sorry
