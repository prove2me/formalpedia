-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_s2_mul_minv
-- name    : DyckAlgebra.DyckRepU.s2_mul_minv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:06:25.515649+00:00
-- url     : https://prove2.me/theorems/1052529a-a331-4c2c-b2fe-c1f21d4f161e
-- title:
--   Dyck Rep U: s2 mul minv
-- statement:
--   The Dyck Rep U construction uses the s2 mul minv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L438-L442
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L438-L442

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.s2_mul_minv : (1 - ρ.s2Elt) * ρ.minv = ρ.w 1 := by sorry
