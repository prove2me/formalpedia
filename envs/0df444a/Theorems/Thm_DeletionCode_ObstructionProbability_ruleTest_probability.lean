-- Prove2me | Theorems.Thm_DeletionCode_ObstructionProbability_ruleTest_probability
-- name    : DeletionCode.ObstructionProbability.ruleTest_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:01:01.057512+00:00
-- url     : https://prove2.me/theorems/bb767bfc-2ca3-4d57-8a52-8efbadfb53c7
-- title:
--   Obstruction Probability: rule Test probability
-- statement:
--   Each fixed independent finite rule set passes all tests with the exact product probability.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L44-L49
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ObstructionProbability.lean#L44-L49

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

theorem DeletionCode.ObstructionProbability.ruleTest_probability (k Q : ℕ) (hQ : 2 ≤ Q) (U : RuleSet k)
    (hU : FiniteGenerating.Independent U) :
    realWeights (Gram (windowLength k)) (ruleTestEvent k Q U) =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ U.card := by sorry
