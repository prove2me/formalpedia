-- Prove2me | Theorems.Thm_BraidsLinksMCG_standard_pure_word_eval_conj_v2
-- name    : BraidsLinksMCG.standard_pure_word_eval_conj_v2
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-27T19:02:35.434981+00:00
-- url     : https://prove2.me/theorems/0c140928-ece0-4436-a9a2-481ff1330d05
-- title:
--   Standard pure braid words evaluate to conjugates of half-twist squares
-- statement:
--   For every standard generator index, the evaluation of its standard pure braid word as geometric half-twists is conjugate in the geometric braid group to the square of the corresponding half-twist. This is the corrected form of the claim that the word 'evaluates to the half-twist square': for non-last indices the word is the pure-braid generator A_{i+1,n+2}, which is conjugate to the half-twist square A_{i+1,i+2} but not equal to it (they are distinct in the abelianization of the pure braid group).
-- source:
--   Corrected variant of BraidsLinksMCG.standard_pure_word_eval_v2 (a747a16f-98e3-4585-be39-1564dc3ea5ed), which is false as stated for non-last indices: the evaluated word is the pure-braid generator A_{i+1,n+2} = σ_n⋯σ_{i+1}σ_i²σ_{i+1}⁻¹⋯σ_n⁻¹, conjugate to but distinct from the half-twist square A_{i+1,i+2}. The last-index case is the proved TarchaBraids.standardPureBraidWord_last_eval_v1 (63461cef-89a0-4511-a630-4904074b86ad).

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1

namespace BraidsLinksMCG

theorem standard_pure_word_eval_conj_v2 (n : Nat) (i : Fin (n + 1)) :
    ∃ c : BraidsLinksMCG.GeomBraidGroup (n + 2),
      FreeGroup.lift (fun j : Fin (n + 2 - 1) => TarchaBraids.halfTwistBraid (n + 2) j)
        (TarchaBraids.braidWordFree (TarchaBraids.standardPureBraidWord (n + 1) i))
        = c * (TarchaBraids.halfTwistBraid (n + 2) i) ^ 2 * c⁻¹ := by sorry

end BraidsLinksMCG
