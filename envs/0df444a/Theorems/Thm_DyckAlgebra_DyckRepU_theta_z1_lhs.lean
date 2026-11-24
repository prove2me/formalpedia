-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_theta_z1_lhs
-- name    : DyckAlgebra.DyckRepU.theta_z1_lhs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:00:25.617289+00:00
-- url     : https://prove2.me/theorems/9b51a83d-dc95-4b18-9525-b4d613d8aee1
-- title:
--   Dyck Rep U: theta z1 lhs
-- statement:
--   The Dyck Rep U construction uses the theta z1 lhs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L461-L470
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L461-L470

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.theta_z1_lhs : ρ.minv * ρ.zz 1 * (1 - ρ.sElt) = ρ.w 1 * ρ.zz 1 := by sorry
