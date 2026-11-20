-- Prove2me | Theorems.Thm_DeletionCode_ObstructionProbability_candidateEvent_eq_union
-- name    : DeletionCode.ObstructionProbability.candidateEvent_eq_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:00:58.135836+00:00
-- url     : https://prove2.me/theorems/d4e6866d-e969-45f7-8a5e-b694976226e9
-- title:
--   Obstruction Probability: candidate Event eq union
-- statement:
--   The Obstruction Probability construction uses the candidate Event eq union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L51-L62
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L51-L62

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

theorem DeletionCode.ObstructionProbability.candidateEvent_eq_union (t k Q R : ℕ) (x : Bits n) :
    candidateEvent t k Q R x =
      ⋃ U : {U : RuleSet k // Candidate t (padBits x) n k R U}, ruleTestEvent k Q U.val := by sorry
