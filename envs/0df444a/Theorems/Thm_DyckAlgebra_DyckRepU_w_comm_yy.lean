-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_w_comm_yy
-- name    : DyckAlgebra.DyckRepU.w_comm_yy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:00:46.20458+00:00
-- url     : https://prove2.me/theorems/d3e93edd-c2f2-4897-96e9-6ce06f27180c
-- title:
--   Dyck Rep U: w comm yy
-- statement:
--   The Dyck Rep U construction uses the w comm yy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L229-L230
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L229-L230

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.w_comm_yy (i : ℕ) : ρ.w i * ρ.yy i = ρ.yy i * ρ.w i := by sorry
