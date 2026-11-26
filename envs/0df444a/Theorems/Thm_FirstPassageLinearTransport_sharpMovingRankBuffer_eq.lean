-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_sharpMovingRankBuffer_eq
-- name    : FirstPassageLinearTransport.sharpMovingRankBuffer_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:16:40.706257+00:00
-- url     : https://prove2.me/theorems/19d00017-83bb-400c-bacf-139e4481391f
-- title:
--   First Passage Linear Transport: sharp Moving Rank Buffer eq
-- statement:
--   The First Passage Linear Transport construction uses the sharp Moving Rank Buffer eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L113-L116
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L113-L116

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.sharpMovingRankBuffer_eq (A : ℕ → ℝ) (M : ℕ) :
    sharpMovingRankBuffer A M =
      firstPassageEntropyGap * movingTerminalRank A M -
        (1 / 2) * Real.logb 2 ((M : ℝ) + 2) := by sorry
