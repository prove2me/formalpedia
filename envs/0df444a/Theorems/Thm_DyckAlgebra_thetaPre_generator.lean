-- Prove2me | Theorems.Thm_DyckAlgebra_thetaPre_generator
-- name    : DyckAlgebra.thetaPre_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:07:44.243868+00:00
-- url     : https://prove2.me/theorems/721a8953-756f-47d6-88a2-28b7cb0efe2c
-- title:
--   Dyck Algebra: theta Pre generator
-- statement:
--   The Dyck Algebra construction uses the theta Pre generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/ThetaDescent.lean#L27-L29
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/ThetaDescent.lean#L27-L29

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_ThetaDescent
set_option autoImplicit true
open DyckAlgebra
universe v
variable {𝕜 : Type*} [Field 𝕜] {q t : 𝕜}
variable {C : Type v} [Ring C] [Algebra 𝕜 C]

theorem DyckAlgebra.thetaPre_generator (thetaGen : Gen → C) (g : Gen) :
    thetaPre thetaGen (FreeAlgebra.ι 𝕜 g) = thetaGen g := by sorry
