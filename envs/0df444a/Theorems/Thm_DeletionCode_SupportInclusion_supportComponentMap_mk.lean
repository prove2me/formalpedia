-- Prove2me | Theorems.Thm_DeletionCode_SupportInclusion_supportComponentMap_mk
-- name    : DeletionCode.SupportInclusion.supportComponentMap_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:08:59.893559+00:00
-- url     : https://prove2.me/theorems/1b937242-d652-4e09-99f5-bcf98cc3d659
-- title:
--   Support Inclusion: support Component Map mk
-- statement:
--   The Support Inclusion construction uses the support Component Map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportInclusion.lean#L47-L50
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportInclusion.lean#L47-L50

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_SupportInclusion
set_option autoImplicit true
open DeletionCode DeletionCode.SupportInclusion
open SignedSupport SupportComponents RuleSetGraph

theorem DeletionCode.SupportInclusion.supportComponentMap_mk {L : ℕ} {Q S : Finset (Gram L → ℤ)}
    (hsub : CoordinateSupportIncluded Q S) (v : RuleSetVertex Q) :
    supportComponentMap hsub (Quotient.mk (ruleSetSetoid Q) v) =
      Quotient.mk (ruleSetSetoid S) ⟨v.val, incident_mono hsub v.property⟩ := by sorry

attribute [defeq] DeletionCode.SupportInclusion.supportComponentMap_mk
