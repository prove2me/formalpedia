-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_lowerSurvivalMass_le_stopped_split
-- name    : FirstPassageLinearTransport.lowerSurvivalMass_le_stopped_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:31:15.246391+00:00
-- url     : https://prove2.me/theorems/121127b2-1c34-5d99-ae67-0c74d98f3dc7
-- title:
--   First Passage Linear Transport: lower Survival Mass le stopped split
-- statement:
--   The First Passage Linear Transport construction uses the lower Survival Mass le stopped split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L325-L387
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L325-L387

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.lowerSurvivalMass_le_stopped_split
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo hi : ℝ) :
    ∀ r z, lowerSurvivalMass p x lo r z ≤
      stoppedUpperMass p x lo hi r z + stoppedHorizonMass p x lo hi r z := by sorry
