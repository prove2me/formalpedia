-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_polylogTerminalRank_pos
-- name    : FirstPassageLinearTransport.polylogTerminalRank_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:57:47.830882+00:00
-- url     : https://prove2.me/theorems/645d73ab-1417-5484-8605-c50382b5f08d
-- title:
--   First Passage Linear Transport: polylog Terminal Rank pos
-- statement:
--   A positive target exponent gives a nonzero terminal rank on every shell.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogTerminalSchedule.lean#L90-L97
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogTerminalSchedule.lean#L90-L97

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.polylogTerminalRank_pos
    {A : ℝ} (hA : 0 < A) (M : ℕ) :
    0 < polylogTerminalRank A M := by sorry
