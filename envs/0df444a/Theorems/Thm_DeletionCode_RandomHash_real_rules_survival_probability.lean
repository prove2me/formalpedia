-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_real_rules_survival_probability
-- name    : DeletionCode.RandomHash.real_rules_survival_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:42.752656+00:00
-- url     : https://prove2.me/theorems/04d254a8-5cd0-451d-9658-5ee46996a393
-- title:
--   Random Hash: real rules survival probability
-- statement:
--   Exact probability that all fixed independent catalogue rules survive.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L119-L125
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L119-L125

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.real_rules_survival_probability (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ)))
    (K₀ : Set (I → ℤ)) (hw : ∀ j, w j ∈ K₀) (Q : ℕ) (hQ : 2 ≤ Q) :
    realWeights I {weights | ∀ j, w j ∈ surviving (realWeightedHash weights) Q K₀} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ Fintype.card J := by sorry
