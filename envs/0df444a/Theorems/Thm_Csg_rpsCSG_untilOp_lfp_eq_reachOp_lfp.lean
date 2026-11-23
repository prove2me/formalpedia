-- Prove2me | Theorems.Thm_Csg_rpsCSG_untilOp_lfp_eq_reachOp_lfp
-- name    : Csg.rpsCSG_untilOp_lfp_eq_reachOp_lfp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T00:48:26.690889+00:00
-- url     : https://prove2.me/theorems/0ba725cc-9352-4618-8944-a1cdf005a7e1
-- title:
--   Csg: rps CSG until Op lfp eq reach Op lfp
-- statement:
--   Both readings of the property -- `Pmax=? [F win2]` and `Pmax=? [!win1 U win2]` -- agree on the
--       nose, not just at `initial`: the two operators have the *same* least fixed point, `rpsVStar`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsUntil.lean#L131-L134
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissorsUntil.lean#L131-L134

import Definitions.Def_Csg_UntilOp
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsUntil
set_option autoImplicit true
open Csg

theorem Csg.rpsCSG_untilOp_lfp_eq_reachOp_lfp :
    (rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero).lfp =
      (rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp := by sorry
