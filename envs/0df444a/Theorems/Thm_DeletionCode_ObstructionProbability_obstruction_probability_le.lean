-- Prove2me | Theorems.Thm_DeletionCode_ObstructionProbability_obstruction_probability_le
-- name    : DeletionCode.ObstructionProbability.obstruction_probability_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:01:05.998417+00:00
-- url     : https://prove2.me/theorems/97489164-464e-4320-94a4-b6f069e839dc
-- title:
--   Obstruction Probability: obstruction probability le
-- statement:
--   The actual rare-obstruction union bound. All coverage, survival, independence,
--   and finiteness used in its proof are derived from verified theorems.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L136-L146
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L136-L146

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

theorem DeletionCode.ObstructionProbability.obstruction_probability_le (t k Q : ℕ) (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (x : Bits n) :
    realWeights (Gram (windowLength k)) (obstructionEvent t k Q x) ≤
      ∑ R ∈ Finset.Icc 2 (cutoff t k),
        (Nat.card {U : RuleSet k // Candidate t (padBits x) n k R U} : ℝ≥0∞) *
          ENNReal.ofReal (2 / (Q : ℝ)) ^ R := by sorry
