-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stoppedHorizonMass_mul_le_time
-- name    : FirstPassageLinearTransport.stoppedHorizonMass_mul_le_time
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:31:06.174374+00:00
-- url     : https://prove2.me/theorems/0008851f-8beb-5c53-aa73-66eabccfc3fc
-- title:
--   First Passage Linear Transport: stopped Horizon Mass mul le time
-- statement:
--   The First Passage Linear Transport construction uses the stopped Horizon Mass mul le time property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L302-L323
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L302-L323

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.stoppedHorizonMass_mul_le_time
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (x : Bool → ℝ) (lo hi : ℝ) :
    ∀ (r : ℕ) (z : ℝ), (r : ℝ) * stoppedHorizonMass p x lo hi r z ≤
      stoppedWalkTime p x lo hi r z := by sorry
