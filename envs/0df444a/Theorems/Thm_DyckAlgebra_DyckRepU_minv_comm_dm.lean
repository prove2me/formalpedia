-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_minv_comm_dm
-- name    : DyckAlgebra.DyckRepU.minv_comm_dm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:06:04.539943+00:00
-- url     : https://prove2.me/theorems/b0214514-e7b7-4eeb-a664-1c2b6b64788e
-- title:
--   Dyck Rep U: minv comm dm
-- statement:
--   The inverse `(1+s*)⁻¹` commutes with `d₋`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L329-L342
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L329-L342

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.minv_comm_dm : ρ.minv * ρ.dm = ρ.dm * ρ.minv := by sorry
