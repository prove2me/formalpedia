-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_theta_y1_rhs
-- name    : DyckAlgebra.DyckRepU.theta_y1_rhs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:00:45.331973+00:00
-- url     : https://prove2.me/theorems/fa68f90b-ddba-4ade-b057-55bbca0b3d91
-- title:
--   Dyck Rep U: theta y1 rhs
-- statement:
--   The Dyck Rep U construction uses the theta y1 rhs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L490-L495
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L490-L495

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.theta_y1_rhs : (1 - ρ.sElt) * ρ.yy 1 * ρ.minv = ρ.w 1 * ρ.yy 1 := by sorry
