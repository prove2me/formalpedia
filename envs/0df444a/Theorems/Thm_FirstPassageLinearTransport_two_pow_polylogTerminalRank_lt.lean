-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_two_pow_polylogTerminalRank_lt
-- name    : FirstPassageLinearTransport.two_pow_polylogTerminalRank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:57:39.999952+00:00
-- url     : https://prove2.me/theorems/55372923-6609-5ef9-9243-47ea56ca7fa5
-- title:
--   First Passage Linear Transport: two pow polylog Terminal Rank lt
-- statement:
--   The integer terminal rank corresponds to the manuscript's fixed
--   polylogarithmic target, with only the factor two introduced by the ceiling.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogTerminalSchedule.lean#L43-L61
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/PolylogTerminalSchedule.lean#L43-L61

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.two_pow_polylogTerminalRank_lt
    {A : ℝ} (hA : 0 ≤ A) (M : ℕ) :
    ((2 ^ polylogTerminalRank A M : ℕ) : ℝ) <
      2 * (((M : ℝ) + 2) ^ A) := by sorry
