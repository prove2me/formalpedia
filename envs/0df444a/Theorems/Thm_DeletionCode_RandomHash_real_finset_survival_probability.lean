-- Prove2me | Theorems.Thm_DeletionCode_RandomHash_real_finset_survival_probability
-- name    : DeletionCode.RandomHash.real_finset_survival_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:17:15.007745+00:00
-- url     : https://prove2.me/theorems/c30e9407-62f2-4781-bd9e-314b573bd672
-- title:
--   Random Hash: real finset survival probability
-- statement:
--   Finite rule sets are counted without adding an ordering or occurrence multiplicity.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L151-L158
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RandomHash.lean#L151-L158

import Definitions.Def_DeletionCode_IntegerTorusMap
import Definitions.Def_DeletionCode_TorusHaar
import Definitions.Def_DeletionCode_CircleUniform
import Definitions.Def_DeletionCode_RandomHash
set_option autoImplicit true
open DeletionCode DeletionCode.RandomHash
open MeasureTheory ProbabilityTheory CircleHash IntegerTorusMap CircleUniform
open scoped BigOperators
variable {I J : Type*} [Fintype I] [Fintype J]

theorem DeletionCode.RandomHash.real_finset_survival_probability (S : Finset (I → ℤ))
    (h : LinearIndependent ℚ (fun w : S => fun i => (w.val i : ℚ)))
    (K₀ : Set (I → ℤ)) (hS : ∀ w ∈ S, w ∈ K₀) (Q : ℕ) (hQ : 2 ≤ Q) :
    realWeights I {weights | ∀ w ∈ S, w ∈ surviving (realWeightedHash weights) Q K₀} =
      ENNReal.ofReal (2 / (Q : ℝ)) ^ S.card := by sorry
