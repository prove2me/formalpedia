-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_weightedSurvivalWordMass_succ
-- name    : FirstPassageLinearTransport.weightedSurvivalWordMass_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:34:37.717873+00:00
-- url     : https://prove2.me/theorems/59274e47-87ed-51de-90d7-2b2ee9e9845a
-- title:
--   First Passage Linear Transport: weighted Survival Word Mass succ
-- statement:
--   The First Passage Linear Transport construction uses the weighted Survival Word Mass succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1574-L1590
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1574-L1590

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.weightedSurvivalWordMass_succ
    (p : ℝ) (x : Bool → ℝ) (lo : ℝ) (r : ℕ) (z : ℝ) :
    weightedSurvivalWordMass p x lo (r + 1) z =
      if lo ≤ z then bernoulliAverage p
        (weightedSurvivalWordMass p x lo r (z + x false))
        (weightedSurvivalWordMass p x lo r (z + x true))
      else 0 := by sorry
