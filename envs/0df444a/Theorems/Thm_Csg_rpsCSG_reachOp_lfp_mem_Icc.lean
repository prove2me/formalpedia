-- Prove2me | Theorems.Thm_Csg_rpsCSG_reachOp_lfp_mem_Icc
-- name    : Csg.rpsCSG_reachOp_lfp_mem_Icc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:12:16.513033+00:00
-- url     : https://prove2.me/theorems/76e4bdb4-43ea-43d7-9d47-b283f8b24e88
-- title:
--   Csg: rps CSG reach Op lfp mem Icc
-- statement:
--   **The headline result.** `(rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp` lies in `[1/3, 2/3]` --
--       the two payoff lemmas above fed into `IntervalCertificate.lean`'s
--       `CSG.reachOp_lfp_mem_Icc_of_certificate`, the first real exercise of that combinator against a
--       concrete instance. `RockPaperScissorsLfp.lean`'s own `rpsCSG_reachOp_lfp_eq` already gives the
--       exact value `1/2`, comfortably inside this sandwich, confirming the interval technique doesn't
--       contradict the exact one -- exactly the cross-check a genuinely new proof route deserves before
--       trusting it for a model where no exact answer is available to check against.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsInterval.lean#L145-L149
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsInterval.lean#L145-L149

import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsInterval
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_reachOp_lfp_mem_Icc :
    rpsLo ≤ (rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp ∧
      (rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp ≤ rpsHi := by sorry
