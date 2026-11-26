-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_polylogTerminalRank_lt_add_one
-- name    : FirstPassageLinearTransport.polylogTerminalRank_lt_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:56:17.758269+00:00
-- url     : https://prove2.me/theorems/48aff20e-9f6c-5ae6-a3cf-2f93d12cdc99
-- title:
--   First Passage Linear Transport: polylog Terminal Rank lt add one
-- statement:
--   The First Passage Linear Transport construction uses the polylog Terminal Rank lt add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogTerminalSchedule.lean#L32-L39
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogTerminalSchedule.lean#L32-L39

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.polylogTerminalRank_lt_add_one
    {A : ℝ} (hA : 0 ≤ A) (M : ℕ) :
    (polylogTerminalRank A M : ℝ) <
      A * Real.logb 2 ((M : ℝ) + 2) + 1 := by sorry
