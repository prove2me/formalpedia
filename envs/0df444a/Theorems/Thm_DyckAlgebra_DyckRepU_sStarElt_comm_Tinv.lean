-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_sStarElt_comm_Tinv
-- name    : DyckAlgebra.DyckRepU.sStarElt_comm_Tinv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:06:09.40407+00:00
-- url     : https://prove2.me/theorems/fb32339f-dc0f-4101-b4e6-08c65dd48867
-- title:
--   Dyck Rep U: s Star Elt comm Tinv
-- statement:
--   The Dyck Rep U construction uses the s Star Elt comm Tinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L392-L396
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L392-L396

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.sStarElt_comm_Tinv (j : ℕ) (hj : 2 ≤ j) :
    ρ.sStarElt * ρ.Tinv j = ρ.Tinv j * ρ.sStarElt := by sorry
