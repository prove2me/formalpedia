-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lowerSurvivalMass_mem_unit
-- name    : FirstPassageLinearTransport.lowerSurvivalMass_mem_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:28:43.792839+00:00
-- url     : https://prove2.me/theorems/b06a6814-c0d6-4c9f-8fff-0a58d2259f62
-- title:
--   First Passage Linear Transport: lower Survival Mass mem unit
-- statement:
--   The First Passage Linear Transport construction uses the lower Survival Mass mem unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L109-L125
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L109-L125

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.lowerSurvivalMass_mem_unit
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo : ℝ) :
    ∀ r z, 0 ≤ lowerSurvivalMass p x lo r z ∧
      lowerSurvivalMass p x lo r z ≤ 1 := by sorry
