-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_theta_y1_dps
-- name    : DyckAlgebra.DyckRepU.theta_y1_dps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T22:57:26.746277+00:00
-- url     : https://prove2.me/theorems/97764791-3a95-46dd-b0b8-4d5c352c4616
-- title:
--   Dyck Rep U: theta y1 dps
-- statement:
--   Second identity of `cor:theta_yz`: the transformed product `y₁ d₊*`
--   is multiplication on the left by the geometric-series factor `w₁`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L515-L517
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L515-L517

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.theta_y1_dps : ρ.Θy1 * ρ.Θdps = ρ.w 1 * ρ.yy 1 * ρ.dps := by sorry
