-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_support_le_reciprocalMaximumSlope
-- name    : FirstPassageLinearTransport.support_le_reciprocalMaximumSlope
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:37:32.136838+00:00
-- url     : https://prove2.me/theorems/a1aa15f7-9512-4a76-aa35-f3e233cecf8e
-- title:
--   First Passage Linear Transport: support le reciprocal Maximum Slope
-- statement:
--   The First Passage Linear Transport construction uses the support le reciprocal Maximum Slope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3193-L3229
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3193-L3229

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.support_le_reciprocalMaximumSlope
    {u : ℝ} (hu : 1 ≤ u) {r : ℕ}
    (hlog : Real.log u ≤
      reciprocalMaximumEpsilon * (r : ℝ) * Real.log 3)
    (v : Fin r → Bool) (hv : ballotWordValue 1 v ≤ u) :
    ((boolSupport v).card : ℝ) ≤
      (3 / 4 - reciprocalMaximumEpsilon) * r := by sorry
