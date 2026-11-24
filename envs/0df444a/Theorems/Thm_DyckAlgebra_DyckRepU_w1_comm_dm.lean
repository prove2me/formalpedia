-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_w1_comm_dm
-- name    : DyckAlgebra.DyckRepU.w1_comm_dm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:05:27.070627+00:00
-- url     : https://prove2.me/theorems/74a822f9-595c-4d32-9cb8-fc318a5a4398
-- title:
--   Dyck Rep U: w1 comm dm
-- statement:
--   The inverse `w₁` commutes with `d₋`, because the derived word `y₁` does.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L244-L252
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L244-L252

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.w1_comm_dm : ρ.w 1 * ρ.dm = ρ.dm * ρ.w 1 := by sorry
