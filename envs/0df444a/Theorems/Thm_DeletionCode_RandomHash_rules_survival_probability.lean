-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_rules_survival_probability
-- name    : DeletionCode.RandomHash.rules_survival_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:13.873974+00:00
-- url     : https://prove2.me/theorems/b4b5a814-c5a8-450d-bfd7-f41990777f85
-- title:
--   Random Hash: rules survival probability
-- statement:
--   For fixed catalogue members, the norm tests are exactly membership in
--   the actual surviving set. No catalogue premise is needed for the norm-only result.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L53-L59
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L53-L59

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.rules_survival_probability (w : J → I → ℤ)
    (h : LinearIndependent ℚ (fun j i => (w j i : ℚ)))
    (K₀ : Set (I → ℤ)) (hw : ∀ j, w j ∈ K₀) (Q : ℕ) (hQ : 2 ≤ Q) :
    volume {weights : I → UnitAddCircle | ∀ j, w j ∈ surviving (weightedHash weights) Q K₀} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ Fintype.card J := by sorry
