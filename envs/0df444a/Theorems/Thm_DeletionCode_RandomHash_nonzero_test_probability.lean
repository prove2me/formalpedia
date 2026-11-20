-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_nonzero_test_probability
-- name    : DeletionCode.RandomHash.nonzero_test_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:19.978656+00:00
-- url     : https://prove2.me/theorems/f6d1b3a7-d898-426c-8ed9-e15033237a1f
-- title:
--   Random Hash: nonzero test probability
-- statement:
--   The manuscript's nonzero-vector assertion is the one-row case.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L72-L78
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L72-L78

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.nonzero_test_probability (w : I → ℤ) (hw : w ≠ 0) (Q : ℕ) (hQ : 2 ≤ Q) :
    volume {weights : I → UnitAddCircle | ‖weightedHash weights w‖ < 1 / (Q : ℝ)} =
      ENNReal.ofReal (2 / (Q : ℝ)) := by sorry
