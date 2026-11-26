-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_movingTerminalRank_lt_add_one
-- name    : FirstPassageLinearTransport.movingTerminalRank_lt_add_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:24:44.350861+00:00
-- url     : https://prove2.me/theorems/d9c72412-676e-4962-965f-0381e006663f
-- title:
--   First Passage Linear Transport: moving Terminal Rank lt add one
-- statement:
--   The First Passage Linear Transport construction uses the moving Terminal Rank lt add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L59-L67
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/MovingEndpointScalars.lean#L59-L67

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.movingTerminalRank_lt_add_one
    {A : ℕ → ℝ} {M : ℕ} (hA : 0 ≤ A M) :
    (movingTerminalRank A M : ℝ) <
      A M * Real.logb 2 ((M : ℝ) + 2) + 1 := by sorry
