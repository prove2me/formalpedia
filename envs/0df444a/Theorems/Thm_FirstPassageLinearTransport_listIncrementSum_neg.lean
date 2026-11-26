-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_listIncrementSum_neg
-- name    : FirstPassageLinearTransport.listIncrementSum_neg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:33:34.42656+00:00
-- url     : https://prove2.me/theorems/1af79e1d-b887-51c7-b7d5-eaca249cce7f
-- title:
--   First Passage Linear Transport: list Increment Sum neg
-- statement:
--   The First Passage Linear Transport construction uses the list Increment Sum neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1213-L1219
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1213-L1219

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.listIncrementSum_neg (x : Bool → ℝ) (l : List Bool) :
    listIncrementSum (fun b => -x b) l = -listIncrementSum x l := by sorry
