-- Prove2me | Theorems.Thm_BraidsLinksMCG_standardGen_image_eq_classical_halfTwist_word_v1
-- name    : BraidsLinksMCG.standardGen_image_eq_classical_halfTwist_word_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-22T08:41:08.615681+00:00
-- url     : https://prove2.me/theorems/bb2b3eec-5ba2-4852-8ce9-2ff66524968b
-- title:
--   A punctured-plane standard generator is the classical pure half-twist word
-- statement:
--   The image in the geometric braid group of the standard punctured-plane loop based at the last strand and encircling puncture j is exactly the classical pure braid word: carry the last strand left across all intervening strands, perform a full twist with strand j, then carry it back. In zero-based indexing this is σ_{n-1}⋯σ_{j+1} σ_j² σ_{j+1}^{-1}⋯σ_{n-1}^{-1}.
-- source:
--   Tarcha Teorema 3.11 / classical pure braid generator identity A_{i,n+1} = (σ_n⋯σ_{i+1}) σ_i² (σ_{i+1}^{-1}⋯σ_n^{-1}), specialised to the explicit standard punctured-plane loops and half-twists already defined in the mission.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1
import Theorems.Thm_TarchaBraids_braidWord_free_eval_v1

namespace BraidsLinksMCG

open TarchaBraids

theorem standardGen_image_eq_classical_halfTwist_word_v1 (n : ℕ) (j : Fin n) :
    (FundamentalGroup.map (configProj (n + 1)) (baseOrdered (n + 1)))
        ((FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)) (standardGen n j))
      =
    FreeGroup.lift
      (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)
      (braidWordFree (standardPureBraidWord n j)) := by sorry

end BraidsLinksMCG
