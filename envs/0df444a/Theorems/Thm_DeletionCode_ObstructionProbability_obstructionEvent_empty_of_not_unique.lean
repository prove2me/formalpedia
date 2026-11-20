-- Prove2me | Theorems.Thm_DeletionCode_ObstructionProbability_obstructionEvent_empty_of_not_unique
-- name    : DeletionCode.ObstructionProbability.obstructionEvent_empty_of_not_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:01:05.918178+00:00
-- url     : https://prove2.me/theorems/64847c06-5d4e-4043-9ac9-8da60124b00c
-- title:
--   Obstruction Probability: obstruction Event empty of not unique
-- statement:
--   A nonunique word cannot be a vertex of the retained conflict graph.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L123-L132
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L123-L132

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

theorem DeletionCode.ObstructionProbability.obstructionEvent_empty_of_not_unique (t k Q : ℕ) (x : Bits n)
    (hx : ¬ KUnique (padBits x) n k) : obstructionEvent t k Q x = ∅ := by sorry
