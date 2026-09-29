-- Prove2me | Theorems.Thm_BraidsLinksMCG_standardGen_image_last_eq_last_halfTwist_square_v1
-- name    : BraidsLinksMCG.standardGen_image_last_eq_last_halfTwist_square_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T07:09:24.60291+00:00
-- url     : https://prove2.me/theorems/a5d61856-8526-4cf8-960c-b185fcf7fd81
-- title:
--   The adjacent standard loop is the square of the final half-twist
-- statement:
--   When the last moving point encircles its immediate neighboring puncture, the resulting pure braid is the square of the final elementary half-twist. This is the adjacent-strand case of the classical pure braid generator formula.
-- source:
--   BraidsLinksMCG.standardGen_image_eq_classical_halfTwist_word_v1, https://beta.prove2.me/theorems/bb2b3eec-5ba2-4852-8ce9-2ff66524968b; Farb and Margalit, A Primer on Mapping Class Groups, pure braid generators formula (Artin generators).

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_strand_extension_v1
open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

namespace BraidsLinksMCG
open TarchaBraids
theorem standardGen_image_last_eq_last_halfTwist_square_v1 (n : ℕ) :
    (FundamentalGroup.map (configProj (n + 2)) (baseOrdered (n + 2)))
      ((FundamentalGroup.mapOfEq (configIncl (n + 1)) (configIncl_base (n + 1)))
        (standardGen (n + 1) (Fin.last n)))
      = (halfTwistBraid (n + 2) (Fin.last n)) ^ 2 := by sorry
end BraidsLinksMCG
