-- Prove2me | Theorems.Thm_BraidsLinksMCG_standard_pure_word_eval_v2
-- name    : BraidsLinksMCG.standard_pure_word_eval_v2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-09-23T20:05:00.632162+00:00
-- url     : https://prove2.me/theorems/a747a16f-98e3-4585-be39-1564dc3ea5ed
-- title:
--   Standard pure braid words evaluate to half twist squares
-- statement:
--   For every standard generator index, evaluation of its standard pure braid word as half twists is the square of the corresponding half twist.
-- source:
--   Generalized form of the target theorem, following its stated source: specialization of the classical pure braid generator formula.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1
open TarchaBraids

namespace BraidsLinksMCG
theorem standard_pure_word_eval_v2 (n : Nat) (i : Fin (n + 1)) :
    FreeGroup.lift (fun j : Fin (n + 2 - 1) => halfTwistBraid (n + 2) j)
      (braidWordFree (standardPureBraidWord (n + 1) i))
      = (halfTwistBraid (n + 2) i) ^ 2 := by sorry
end BraidsLinksMCG
