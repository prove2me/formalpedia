-- Prove2me | Theorems.Thm_DeletionCode_SupportInclusion_hit_component_count_le
-- name    : DeletionCode.SupportInclusion.hit_component_count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:13:11.612232+00:00
-- url     : https://prove2.me/theorems/d335b8da-fe42-4df1-8088-b3b22fd92f00
-- title:
--   Support Inclusion: hit component count le
-- statement:
--   Vertex witnesses suffice to bound any selected collection of components
--   of the larger signed-support graph. No injective assignment is assumed.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportInclusion.lean#L80-L88
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportInclusion.lean#L80-L88

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SupportInclusion
set_option autoImplicit true
open DeletionCode DeletionCode.SupportInclusion
open SignedSupport SupportComponents RuleSetGraph

theorem DeletionCode.SupportInclusion.hit_component_count_le {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) (P : RuleSetComponents S → Prop)
    (hhit : ∀ C, P C → ∃ v : RuleSetVertex Q,
      supportComponentMap hsub (Quotient.mk (ruleSetSetoid Q) v) = C) :
    Fintype.card {C : RuleSetComponents S // P C} ≤ componentCount Q := by sorry
