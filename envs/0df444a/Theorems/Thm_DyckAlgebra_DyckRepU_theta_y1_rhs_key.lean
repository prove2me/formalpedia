-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_theta_y1_rhs_key
-- name    : DyckAlgebra.DyckRepU.theta_y1_rhs_key
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:07:15.721207+00:00
-- url     : https://prove2.me/theorems/0a3d965a-21a6-40e7-b94c-d8d4c99e0362
-- title:
--   Dyck Rep U: theta y1 rhs key
-- statement:
--   The Dyck Rep U construction uses the theta y1 rhs key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L483-L488
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L483-L488

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.theta_y1_rhs_key :
    (1 - ρ.sElt) * ρ.yy 1 = ρ.w 1 * ρ.yy 1 * (1 + ρ.sStarElt) := by sorry
