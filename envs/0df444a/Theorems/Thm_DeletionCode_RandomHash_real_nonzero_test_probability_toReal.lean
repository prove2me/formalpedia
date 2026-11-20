-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_real_nonzero_test_probability_toReal
-- name    : DeletionCode.RandomHash.real_nonzero_test_probability_toReal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:18.015026+00:00
-- url     : https://prove2.me/theorems/7a07f18d-7155-408c-a7f4-45c837d2aa21
-- title:
--   Random Hash: real nonzero test probability to Real
-- statement:
--   The Random Hash construction uses the real nonzero test probability to Real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L144-L148
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L144-L148

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.real_nonzero_test_probability_toReal (w : I → ℤ) (hw : w ≠ 0) (Q : ℕ) (hQ : 2 ≤ Q) :
    (realWeights I {weights | ‖realWeightedHash weights w‖ < 1 / (Q : ℝ)}).toReal =
      2 / (Q : ℝ) := by sorry
