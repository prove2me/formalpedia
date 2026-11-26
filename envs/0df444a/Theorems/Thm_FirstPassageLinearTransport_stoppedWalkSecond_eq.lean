-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stoppedWalkSecond_eq
-- name    : FirstPassageLinearTransport.stoppedWalkSecond_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:30:55.744637+00:00
-- url     : https://prove2.me/theorems/b899aa08-d002-5594-9a4e-e883cb11d369
-- title:
--   First Passage Linear Transport: stopped Walk Second eq
-- statement:
--   The First Passage Linear Transport construction uses the stopped Walk Second eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L180-L212
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L180-L212

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.stoppedWalkSecond_eq
    {p v : ℝ} (x : Bool → ℝ) (lo hi : ℝ)
    (hcenter : bernoulliAverage p (x false) (x true) = 0)
    (hvariance : bernoulliAverage p ((x false) ^ 2) ((x true) ^ 2) = v) :
    ∀ r z, stoppedWalkSecond p x lo hi r z =
      z ^ 2 + v * stoppedWalkTime p x lo hi r z := by sorry
