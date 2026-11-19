-- Prove2me | Theorems.Thm_DeletionCode_RuleReconstruction_recovered_bubble_spectrum
-- name    : DeletionCode.RuleReconstruction.recovered_bubble_spectrum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:19:02.585205+00:00
-- url     : https://prove2.me/theorems/43c816cb-477d-449f-bec8-c77324658225
-- title:
--   Rule Reconstruction: recovered bubble spectrum
-- statement:
--   The Rule Reconstruction construction uses the recovered bubble spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleReconstruction.lean#L54-L64
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleReconstruction.lean#L54-L64

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_RecordSerialization
import Definitions.Def_DeletionCode_RuleReconstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RuleReconstruction
open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators

theorem DeletionCode.RuleReconstruction.recovered_bubble_spectrum {ν k : ℕ} (E : EditedFamily (Fin ν) k)
    (rank : Fin ν → ℕ) (b : Fin ν) :
    bubbleSpectrum (recoveredFamily k rank (dataOfFamily E)) (windowLength k) b =
      bubbleSpectrum E.family (windowLength k) b := by sorry
