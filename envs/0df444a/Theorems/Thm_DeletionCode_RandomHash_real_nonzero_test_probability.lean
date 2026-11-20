-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_real_nonzero_test_probability
-- name    : DeletionCode.RandomHash.real_nonzero_test_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:45:51.985227+00:00
-- url     : https://prove2.me/theorems/87e902ad-d2af-492a-b1a5-9d2d9059c1f1
-- title:
--   Random Hash: real nonzero test probability
-- statement:
--   The Random Hash construction uses the real nonzero test probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L127-L133
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L127-L133

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.real_nonzero_test_probability (w : I → ℤ) (hw : w ≠ 0) (Q : ℕ) (hQ : 2 ≤ Q) :
    realWeights I {weights | ‖realWeightedHash weights w‖ < 1 / (Q : ℝ)} =
      ENNReal.ofReal (2 / (Q : ℝ)) := by sorry
