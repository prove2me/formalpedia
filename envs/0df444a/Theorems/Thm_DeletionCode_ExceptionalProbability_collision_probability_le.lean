-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalProbability_collision_probability_le
-- name    : DeletionCode.ExceptionalProbability.collision_probability_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:10.895206+00:00
-- url     : https://prove2.me/theorems/1bc0ccfc-dd77-4e70-94c2-a7baa62d7005
-- title:
--   Exceptional Probability: collision probability le
-- statement:
--   A label collision is contained in the strict norm test on a derived
--   nonzero spectrum difference, whose probability is exactly 2/Q.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean#L84-L96
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean#L84-L96

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

theorem DeletionCode.ExceptionalProbability.collision_probability_le (k Q : ℕ) (x y : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n)
    (hQ : 2 ≤ Q) (hxy : x ≠ y) :
    realWeights (Gram (windowLength k)) (collisionEvent k Q x y) ≤
      ENNReal.ofReal (2 / (Q : ℝ)) := by sorry
