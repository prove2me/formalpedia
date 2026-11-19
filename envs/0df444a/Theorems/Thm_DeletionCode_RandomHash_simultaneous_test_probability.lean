-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_simultaneous_test_probability
-- name    : DeletionCode.RandomHash.simultaneous_test_probability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:37:20.953365+00:00
-- url     : https://prove2.me/theorems/56cd8dae-eaf6-4cb9-b5d1-d890d2a43b89
-- title:
--   Random Hash: simultaneous test probability
-- statement:
--   Exact simultaneous survival probability, including Q = 2 and an empty
--   independent family. The test is strict, as in the manuscript.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L39-L49
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L39-L49

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.simultaneous_test_probability (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (Q : ℕ) (hQ : 2 ≤ Q) :
    volume {weights : I → UnitAddCircle | ∀ j, ‖weightedHash weights (w j)‖ < 1 / (Q : ℝ)} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ Fintype.card J := by sorry
