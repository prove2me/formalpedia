-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_sum_weightedSurvivalFactor_eq
-- name    : FirstPassageLinearTransport.sum_weightedSurvivalFactor_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:35:23.186784+00:00
-- url     : https://prove2.me/theorems/c0c8ed99-7dc6-4df9-b39c-f1a918112436
-- title:
--   First Passage Linear Transport: sum weighted Survival Factor eq
-- statement:
--   The First Passage Linear Transport construction uses the sum weighted Survival Factor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1833-L1839
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1833-L1839

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.sum_weightedSurvivalFactor_eq
    (p : ℝ) (x : Bool → ℝ) (lo z : ℝ) (r : ℕ) :
    ∑ v : Fin r → Bool, weightedSurvivalFactor p x lo z v =
      weightedSurvivalWordMass p x lo r z := by sorry
