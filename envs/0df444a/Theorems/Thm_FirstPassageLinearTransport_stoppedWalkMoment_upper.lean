-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stoppedWalkMoment_upper
-- name    : FirstPassageLinearTransport.stoppedWalkMoment_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:31:01.497642+00:00
-- url     : https://prove2.me/theorems/46897e20-125a-4bf1-90a4-ecb9ac9d7b6b
-- title:
--   First Passage Linear Transport: stopped Walk Moment upper
-- statement:
--   The First Passage Linear Transport construction uses the stopped Walk Moment upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L214-L247
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L214-L247

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.stoppedWalkMoment_upper
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    {x : Bool → ℝ} (hx : ∀ b, |x b| ≤ 1) {lo hi : ℝ} :
    ∀ r z, lo - 1 ≤ z → z ≤ hi + 1 →
      stoppedWalkSecond p x lo hi r z ≤
        (lo + hi) * stoppedWalkMean p x lo hi r z -
          (lo - 1) * (hi + 1) := by sorry
