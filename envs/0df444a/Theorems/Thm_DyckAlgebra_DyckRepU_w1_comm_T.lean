-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_w1_comm_T
-- name    : DyckAlgebra.DyckRepU.w1_comm_T
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:05:00.299079+00:00
-- url     : https://prove2.me/theorems/896b4798-a1e6-4f75-bff0-b46cffae430b
-- title:
--   Dyck Rep U: w1 comm T
-- statement:
--   The Dyck Rep U construction uses the w1 comm T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L235-L241
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L235-L241

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.w1_comm_T (j : ℕ) (hj : 2 ≤ j) : ρ.w 1 * ρ.T j = ρ.T j * ρ.w 1 := by sorry
