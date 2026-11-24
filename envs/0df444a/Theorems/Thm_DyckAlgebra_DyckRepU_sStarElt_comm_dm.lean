-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_sStarElt_comm_dm
-- name    : DyckAlgebra.DyckRepU.sStarElt_comm_dm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:05:41.562797+00:00
-- url     : https://prove2.me/theorems/1e8b36c8-557e-4885-b547-a268ecfb64d8
-- title:
--   Dyck Rep U: s Star Elt comm dm
-- statement:
--   The starred correction term also commutes with `d₋`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L312-L326
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L312-L326

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.sStarElt_comm_dm : ρ.sStarElt * ρ.dm = ρ.dm * ρ.sStarElt := by sorry
