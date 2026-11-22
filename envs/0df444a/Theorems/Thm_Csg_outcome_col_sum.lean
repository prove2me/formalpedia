-- Prove2me | Theorems.Thm_Csg_outcome_col_sum
-- name    : Csg.outcome_col_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:55:31.060977+00:00
-- url     : https://prove2.me/theorems/1bd33baf-6d28-459c-a664-258964f9b36b
-- title:
--   Csg: outcome col sum
-- statement:
--   Symmetric counterpart of `outcome_row_sum`, for a fixed column action.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L132-L135
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/RockPaperScissors.lean#L132-L135

import Definitions.Def_Csg_BoundedReachability
import Definitions.Def_Csg_MatchingPennies
import Definitions.Def_Csg_RockPaperScissors
set_option autoImplicit true
open Csg

theorem Csg.outcome_col_sum (a2 : RPSAction) (v : RPSState → ℝ) :
    v (outcome .rock a2) + v (outcome .paper a2) + v (outcome .scissors a2) =
      v .win1 + v .win2 + v .draw := by sorry
