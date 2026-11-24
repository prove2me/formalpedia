-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_minv_mul_dps_pow
-- name    : DyckAlgebra.DyckRepU.minv_mul_dps_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:07:11.693162+00:00
-- url     : https://prove2.me/theorems/28effbab-7fd2-4dbc-9c3b-fa6370313dfe
-- title:
--   Dyck Rep U: minv mul dps pow
-- statement:
--   The Dyck Rep U construction uses the minv mul dps pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean#L93-L102
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean#L93-L102

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_PreserveKernel
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.minv_mul_dps_pow (j : ℕ) (e0 : ρ.carrier)
    (hsStar : ρ.sStarElt * ρ.dps ^ j * e0 = 0) :
    ρ.minv * ρ.dps ^ j * e0 = ρ.dps ^ j * e0 := by sorry
