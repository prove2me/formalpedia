-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_s2_mul_left_inv
-- name    : DyckAlgebra.DyckRepU.s2_mul_left_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:20:29.313381+00:00
-- url     : https://prove2.me/theorems/063b4f34-22fa-4792-9f69-7eca60b64d07
-- title:
--   Dyck Rep U: s2 mul left inv
-- statement:
--   The Dyck Rep U construction uses the s2 mul left inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L453-L456
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L453-L456

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.s2_mul_left_inv : (ρ.minv * (1 + ρ.u • ρ.yy 1)) * (1 - ρ.s2Elt) = 1 := by sorry
