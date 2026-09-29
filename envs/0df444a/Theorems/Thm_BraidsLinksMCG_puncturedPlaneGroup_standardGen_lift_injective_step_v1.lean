-- Prove2me | Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_standardGen_lift_injective_step_v1
-- name    : BraidsLinksMCG.puncturedPlaneGroup_standardGen_lift_injective_step_v1
-- status  : Open
-- author  : @WillR
-- created : 2026-09-23T22:44:29.989445+00:00
-- url     : https://prove2.me/theorems/f63f0a21-a4e0-4af6-ae28-f1671f1a9399
-- title:
--   Adding a puncture introduces no relation among the standard loops
-- statement:
--   Assuming the named loops freely generate the fundamental group of the plane with n punctures, the canonical homomorphism from the free group on the named loops to the fundamental group after adding one puncture is injective. Thus no nontrivial reduced word in the n+1 standard loops becomes null-homotopic. This is the no-relations part of the matched induction step.
-- source:
--   Hatcher, Algebraic Topology, Example 1.21 and Theorem 1.20 (Seifert--van Kampen); injective half of the standard-loop basis computation.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops

namespace BraidsLinksMCG

theorem puncturedPlaneGroup_standardGen_lift_injective_step_v1 (n : ℕ)
    (ih : ∃ e : PuncturedPlaneGroup n ≃* FreeGroup (Fin n),
      ∀ j : Fin n, e (standardGen n j) = FreeGroup.of j) :
    Function.Injective (FreeGroup.lift (standardGen (n + 1))) := by sorry

end BraidsLinksMCG
