-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_real_simultaneous_test_probability
-- name    : DeletionCode.RandomHash.real_simultaneous_test_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:39.422971+00:00
-- url     : https://prove2.me/theorems/a26bcc02-fff9-475c-a8ce-2eb29f52573f
-- title:
--   Random Hash: real simultaneous test probability
-- statement:
--   The Random Hash construction uses the real simultaneous test probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L106-L116
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L106-L116

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.real_simultaneous_test_probability (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (Q : ℕ) (hQ : 2 ≤ Q) :
    realWeights I {weights | ∀ j, ‖realWeightedHash weights (w j)‖ < 1 / (Q : ℝ)} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ Fintype.card J := by sorry
