-- Prove2me | Theorems.Thm_BraidsLinksMCG_standardGen_image_strandExtension_conjugate_v1
-- name    : BraidsLinksMCG.standardGen_image_strandExtension_conjugate_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T07:09:41.957992+00:00
-- url     : https://prove2.me/theorems/2273a291-a4e8-43a8-b38b-527095999a64
-- title:
--   Adding a rightmost strand conjugates the standard-loop braid image
-- statement:
--   Under addition of one stationary rightmost strand, the braid represented by an earlier standard puncture loop becomes the conjugate of its previous braid image by the new final half-twist. This is the geometric strand-addition recurrence matching the classical pure braid word recurrence.
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
theorem standardGen_image_strandExtension_conjugate_v1 (n : ℕ) (j : Fin n) :
    (FundamentalGroup.map (configProj (n + 2)) (baseOrdered (n + 2)))
      ((FundamentalGroup.mapOfEq (configIncl (n + 1)) (configIncl_base (n + 1)))
        (standardGen (n + 1) j.castSucc))
      = halfTwistBraid (n + 2) (Fin.last n) *
        (FundamentalGroup.mapOfEq (TarchaBraids.StrandExtension.addU (n + 1))
          (TarchaBraids.StrandExtension.addU_base (n + 1)))
          ((FundamentalGroup.map (configProj (n + 1)) (baseOrdered (n + 1)))
            ((FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)) (standardGen n j))) *
        (halfTwistBraid (n + 2) (Fin.last n))⁻¹ := by sorry
end BraidsLinksMCG
