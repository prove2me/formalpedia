-- Prove2me | Theorems.Thm_DeletionCode_ObstructionProbability_obstructionEvent_subset_union
-- name    : DeletionCode.ObstructionProbability.obstructionEvent_subset_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:00:38.346841+00:00
-- url     : https://prove2.me/theorems/335b27ca-7103-48ca-8605-e79f1c0bf3ce
-- title:
--   Obstruction Probability: obstruction Event subset union
-- statement:
--   Every concrete graph obstruction supplies one of the fixed candidate survival events.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L87-L101
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L87-L101

import Definitions.Def_DeletionCode_VerifiedConflictGraphWitness
import Definitions.Def_DeletionCode_WitnessCounting
import Definitions.Def_DeletionCode_RandomHash
import Definitions.Def_DeletionCode_ObstructionProbability
set_option autoImplicit true
open DeletionCode DeletionCode.ObstructionProbability
open MeasureTheory Windows HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph
open CircleHash CircleUniform ConflictGraphWitness WitnessCounting
open scoped BigOperators ENNReal
variable {n : ℕ}

theorem DeletionCode.ObstructionProbability.obstructionEvent_subset_union (t k Q : ℕ) (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (x : Bits n) :
    obstructionEvent t k Q x ⊆
      ⋃ R ∈ Finset.Icc 2 (cutoff t k), candidateEvent t k Q R x := by sorry
