-- Prove2me | Theorems.Thm_DeletionCode_ObstructionProbability_obstruction_probability_le_of_unique
-- name    : DeletionCode.ObstructionProbability.obstruction_probability_le_of_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:00:19.251182+00:00
-- url     : https://prove2.me/theorems/29c0d482-7878-4f54-a0cb-6692cc4e7861
-- title:
--   Obstruction Probability: obstruction probability le of unique
-- statement:
--   The Obstruction Probability construction uses the obstruction probability le of unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L103-L120
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L103-L120

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

theorem DeletionCode.ObstructionProbability.obstruction_probability_le_of_unique (t k Q : ℕ) (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (x : Bits n) (hx : KUnique (padBits x) n k) :
    realWeights (Gram (windowLength k)) (obstructionEvent t k Q x) ≤
      ∑ R ∈ Finset.Icc 2 (cutoff t k),
        (Nat.card {U : RuleSet k // Candidate t (padBits x) n k R U} : ℝ≥0∞) *
          ENNReal.ofReal (2 / (Q : ℝ)) ^ R := by sorry
