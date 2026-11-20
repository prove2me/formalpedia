-- Prove2me | Theorems.Thm_DeletionCode_RuleReconstruction_recovered_rule_spectrum
-- name    : DeletionCode.RuleReconstruction.recovered_rule_spectrum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:19:15.661878+00:00
-- url     : https://prove2.me/theorems/bd67789d-d9b7-4e87-90e3-1b48d544aa51
-- title:
--   Rule Reconstruction: recovered rule spectrum
-- statement:
--   The Rule Reconstruction construction uses the recovered rule spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleReconstruction.lean#L66-L74
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleReconstruction.lean#L66-L74

import Definitions.Def_DeletionCode_SignedSupport
import Definitions.Def_DeletionCode_RecordSerialization
import Definitions.Def_DeletionCode_RuleReconstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RuleReconstruction
open Windows HeaderRecovery RootSelection SignedSupport RecordSerialization GeneratingModel
open scoped BigOperators

theorem DeletionCode.RuleReconstruction.recovered_rule_spectrum {ν k : ℕ} (E : EditedFamily (Fin ν) k)
    (rank : Fin ν → ℕ) (bubbles : Finset (Fin ν)) :
    ruleSpectrum (recoveredFamily k rank (dataOfFamily E)) (windowLength k) bubbles =
      ruleSpectrum E.family (windowLength k) bubbles := by sorry
