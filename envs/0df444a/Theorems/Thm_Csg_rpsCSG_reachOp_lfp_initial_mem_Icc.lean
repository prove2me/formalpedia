-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachOp_lfp_initial_mem_Icc
-- name    : Csg.rpsCSG_reachOp_lfp_initial_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T00:51:53.78885+00:00
-- url     : https://prove2.me/theorems/30986b2a-9212-4a61-a7c6-2459b8e0a01d
-- title:
--   Csg: rps CSG reach Op lfp initial mem Icc
-- statement:
--   The concrete numeric consequence at `initial`: `1/3 ≤ 1/2 ≤ 2/3`, the interval certificate's
--       sandwich next to the exact value it brackets.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsInterval.lean#L153-L156
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsInterval.lean#L153-L156

import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsInterval
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachOp_lfp_initial_mem_Icc :
    (1 : ℝ) / 3 ≤ ((rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp RPSState.initial : ℝ) ∧
      ((rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp RPSState.initial : ℝ) ≤ 2 / 3 := by sorry
