-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_movingRankBuffer_eq
-- name    : FirstPassageLinearTransport.movingRankBuffer_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:20:39.349225+00:00
-- url     : https://prove2.me/theorems/de937ba5-aca1-446c-aac0-dab666188c34
-- title:
--   First Passage Linear Transport: moving Rank Buffer eq
-- statement:
--   The First Passage Linear Transport construction uses the moving Rank Buffer eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L107-L111
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L107-L111

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.movingRankBuffer_eq (A : ℕ → ℝ) (M : ℕ) :
    movingRankBuffer A M =
      firstPassageEntropyGap * movingTerminalRank A M -
        (1 / 2) * Real.logb 2 ((M : ℝ) + 2) -
        Real.logb 2 (Real.log ((M : ℝ) + 3)) := by sorry
