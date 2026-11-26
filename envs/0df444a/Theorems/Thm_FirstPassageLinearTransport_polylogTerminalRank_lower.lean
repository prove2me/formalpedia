-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_polylogTerminalRank_lower
-- name    : FirstPassageLinearTransport.polylogTerminalRank_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:56:15.482678+00:00
-- url     : https://prove2.me/theorems/e9e63ff5-fdb3-57e8-82c7-d851ece72d25
-- title:
--   First Passage Linear Transport: polylog Terminal Rank lower
-- statement:
--   The First Passage Linear Transport construction uses the polylog Terminal Rank lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogTerminalSchedule.lean#L27-L30
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogTerminalSchedule.lean#L27-L30

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.polylogTerminalRank_lower (A : ℝ) (M : ℕ) :
    A * Real.logb 2 ((M : ℝ) + 2) ≤
      (polylogTerminalRank A M : ℝ) := by sorry
