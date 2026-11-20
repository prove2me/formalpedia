-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalProbability_exceptional_probability_le
-- name    : DeletionCode.ExceptionalProbability.exceptional_probability_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:43:07.120733+00:00
-- url     : https://prove2.me/theorems/e63033a9-1f9a-4328-85a5-c69004382aab
-- title:
--   Exceptional Probability: exceptional probability le
-- statement:
--   Probability half of `lem:nonsep`, before its separate combinatorial
--   candidate-count estimate. Partners are actual finite words, not records,
--   and are not assumed unique.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean#L109-L127
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean#L109-L127

import Definitions.Def_DeletionCode_RandomHash
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_ExceptionalProbability
set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform
open ConflictGraphWitness
open scoped BigOperators
variable {n : ℕ}

theorem DeletionCode.ExceptionalProbability.exceptional_probability_le (t k Q : ℕ) (x : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n) (hQ : 2 ≤ Q) :
    realWeights (Gram (windowLength k))
        {weights | FiniteConflictGraph.Exceptional t k
          (wordLabel Q (realWeightedHash weights)) x} ≤
      (candidatePartners t k x).card * ENNReal.ofReal (2 / (Q : ℝ)) := by sorry
