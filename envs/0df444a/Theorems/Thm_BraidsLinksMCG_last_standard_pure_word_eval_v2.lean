-- Prove2me | Theorems.Thm_BraidsLinksMCG_last_standard_pure_word_eval_v2
-- name    : BraidsLinksMCG.last_standard_pure_word_eval_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-23T19:55:18.280764+00:00
-- url     : https://prove2.me/theorems/63b49045-530f-417c-ade1-6e3648c3a521
-- title:
--   The final standard pure braid word evaluates to the final half-twist square
-- statement:
--   For the standard pure braid word associated with the last puncture, its evaluation as geometric half-twists is the square of the final half-twist.
-- source:
--   Specialization of the classical pure braid generator formula.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1
open TarchaBraids

namespace BraidsLinksMCG
theorem last_standard_pure_word_eval_v2 (n : Nat) :
    FreeGroup.lift (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
      (braidWordFree (standardPureBraidWord (n + 1) (Fin.last n)))
      = (halfTwistBraid (n + 2) (Fin.last n)) ^ 2 := by sorry
end BraidsLinksMCG
