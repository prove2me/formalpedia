-- Prove2me | Theorems.Thm_DeletionCode_VerifiedConflictGraphWitness_listLetters_ofFn
-- name    : DeletionCode.VerifiedConflictGraphWitness.listLetters_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:59:38.534244+00:00
-- url     : https://prove2.me/theorems/0b35cb78-d57f-4678-89eb-b8dd4825ea2a
-- title:
--   Verified Conflict Graph Witness: list Letters of Fn
-- statement:
--   The Verified Conflict Graph Witness construction uses the list Letters of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/VerifiedConflictGraphWitness.lean#L15-L20
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/VerifiedConflictGraphWitness.lean#L15-L20

import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_BubbleCatalogue
import Definitions.Def_DeletionCode_SeparatedTraceCoverage
import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
set_option autoImplicit true
open DeletionCode DeletionCode.VerifiedConflictGraphWitness
open Windows HeaderRecovery CatalogueWords AlignmentTrace
open ConflictGraphWitness SignedSupport SignedRuleCount RuleSetGraph WitnessCases

theorem DeletionCode.VerifiedConflictGraphWitness.listLetters_ofFn {n : ℕ} (x : Bits n) :
    listLetters (List.ofFn x) = padBits x := by sorry
