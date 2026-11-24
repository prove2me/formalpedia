-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_theta_z1_dp
-- name    : DyckAlgebra.DyckRepU.theta_z1_dp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:06:48.501798+00:00
-- url     : https://prove2.me/theorems/2c8e99b0-169e-4258-a4cc-e71835a334fa
-- title:
--   Dyck Rep U: theta z1 dp
-- statement:
--   First identity of `cor:theta_yz`: the transformed product `z₁ d₊`
--   is multiplication on the left by the geometric-series factor `w₁`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L509-L511
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L509-L511

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.theta_z1_dp : ρ.Θz1 * ρ.Θdp = ρ.w 1 * ρ.zz 1 * ρ.dp := by sorry
