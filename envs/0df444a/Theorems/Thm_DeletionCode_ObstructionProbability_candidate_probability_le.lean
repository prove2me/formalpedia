-- Prove2me | Theorems.Thm_DeletionCode_ObstructionProbability_candidate_probability_le
-- name    : DeletionCode.ObstructionProbability.candidate_probability_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:00:35.663656+00:00
-- url     : https://prove2.me/theorems/3d1ad746-e841-4e06-9bbf-e59fa8e2098b
-- title:
--   Obstruction Probability: candidate probability le
-- statement:
--   The fixed-size bound counts underlying finite rule sets, without ordering their rules.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L65-L84
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L65-L84

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

theorem DeletionCode.ObstructionProbability.candidate_probability_le (t k Q R : ℕ) (ht : 1 ≤ t) (hR : 1 ≤ R)
    (x : Bits n) (hx : KUnique (padBits x) n k) (hQ : 2 ≤ Q) :
    realWeights (Gram (windowLength k)) (candidateEvent t k Q R x) ≤
      (Nat.card {U : RuleSet k // Candidate t (padBits x) n k R U} : ℝ≥0∞) *
        ENNReal.ofReal (2 / (Q : ℝ)) ^ R := by sorry
