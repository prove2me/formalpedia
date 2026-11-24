-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_sElt_comm_dm
-- name    : DyckAlgebra.DyckRepU.sElt_comm_dm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:05:11.534213+00:00
-- url     : https://prove2.me/theorems/47e8d4be-cb02-42bc-8d16-40cc302289d3
-- title:
--   Dyck Rep U: s Elt comm dm
-- statement:
--   The correction term `s` commutes with `d₋`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L255-L267
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L255-L267

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.sElt_comm_dm : ρ.sElt * ρ.dm = ρ.dm * ρ.sElt := by sorry
