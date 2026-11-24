-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_sStar_acts_as_0
-- name    : DyckAlgebra.DyckRepU.sStar_acts_as_0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:06:59.798602+00:00
-- url     : https://prove2.me/theorems/7c946bbf-32f5-42a4-8312-d0294121bcef
-- title:
--   Dyck Rep U: s Star acts as 0
-- statement:
--   The Dyck Rep U construction uses the s Star acts as 0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean#L80-L88
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean#L80-L88

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_PreserveKernel
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.sStar_acts_as_0 (k : ℕ) (_hk : 1 ≤ k) (e0 : ρ.carrier)
    (hq : q ≠ 0)
    (hI2 : ρ.yy 1 * ρ.dps ^ k * e0
        = (-(q ^ k)⁻¹) • (ρ.dp * ρ.dps ^ (k - 1) * e0))
    (hQ2 : ρ.zz 1 * (ρ.dp * ρ.dps ^ (k - 1) * e0)
        = (-(q ^ k)) • (ρ.yy 1 * ρ.dps ^ k * e0)) :
    ρ.sStarElt * ρ.dps ^ k * e0 = 0 := by sorry
