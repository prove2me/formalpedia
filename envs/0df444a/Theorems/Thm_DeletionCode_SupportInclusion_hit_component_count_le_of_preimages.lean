-- Prove2me | Theorems.Thm_DeletionCode_SupportInclusion_hit_component_count_le_of_preimages
-- name    : DeletionCode.SupportInclusion.hit_component_count_le_of_preimages
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:13:04.302806+00:00
-- url     : https://prove2.me/theorems/47a89ee7-744c-4eb9-8fa8-9a94fdedce67
-- title:
--   Support Inclusion: hit component count le of preimages
-- statement:
--   Components hit by a smaller support union cannot outnumber that union's
--   components. The preimage condition is witnessed at the quotient level.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportInclusion.lean#L58-L76
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportInclusion.lean#L58-L76

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SupportInclusion
set_option autoImplicit true
open DeletionCode DeletionCode.SupportInclusion
open SignedSupport SupportComponents RuleSetGraph

theorem DeletionCode.SupportInclusion.hit_component_count_le_of_preimages {L : ℕ}
    {Q S : Finset (Gram L → ℤ)} (hsub : CoordinateSupportIncluded Q S)
    (P : RuleSetComponents S → Prop)
    (hhit : ∀ C, P C → ∃ D, supportComponentMap hsub D = C) :
    Fintype.card {C : RuleSetComponents S // P C} ≤ componentCount Q := by sorry
