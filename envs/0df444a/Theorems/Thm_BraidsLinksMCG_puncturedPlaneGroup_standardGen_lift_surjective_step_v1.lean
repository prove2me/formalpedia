-- Prove2me | Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_standardGen_lift_surjective_step_v1
-- name    : BraidsLinksMCG.puncturedPlaneGroup_standardGen_lift_surjective_step_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T22:44:58.552099+00:00
-- url     : https://prove2.me/theorems/5cbb403f-e1aa-401c-b774-4154a1ce2ad6
-- title:
--   The standard loops generate after adding one puncture
-- statement:
--   Assuming the named loops freely generate the fundamental group of the plane with n punctures, every loop class after adding one puncture is a word in the n+1 named standard loops. This is the generation part of the matched induction step; unlike injectivity, it does not assert that the word representation is unique.
-- source:
--   Hatcher, Algebraic Topology, Example 1.21 and Theorem 1.20 (Seifert--van Kampen); surjective half of the standard-loop basis computation.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops

namespace BraidsLinksMCG

theorem puncturedPlaneGroup_standardGen_lift_surjective_step_v1 (n : ℕ)
    (ih : ∃ e : PuncturedPlaneGroup n ≃* FreeGroup (Fin n),
      ∀ j : Fin n, e (standardGen n j) = FreeGroup.of j) :
    Function.Surjective (FreeGroup.lift (standardGen (n + 1))) := by sorry

end BraidsLinksMCG
