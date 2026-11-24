-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_w1_sub_one
-- name    : DyckAlgebra.DyckRepU.w1_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:06:54.264482+00:00
-- url     : https://prove2.me/theorems/468531d0-9e87-4402-aa54-ad15b743e304
-- title:
--   Dyck Rep U: w1 sub one
-- statement:
--   The Dyck Rep U construction uses the w1 sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean#L35-L38
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean#L35-L38

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_PreserveKernel
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.w1_sub_one : ρ.w 1 - 1 = -(ρ.u • (ρ.w 1 * ρ.yy 1)) := by sorry
