-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_theta_Q2
-- name    : DyckAlgebra.DyckRepU.theta_Q2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:06:44.954215+00:00
-- url     : https://prove2.me/theorems/d7804a7d-d462-4309-8499-bcbc9d33142c
-- title:
--   Dyck Rep U: theta Q2
-- statement:
--   The Dyck Rep U construction uses the theta Q2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L500-L505
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L500-L505

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.theta_Q2 : ρ.Θz1 * ρ.Θdp = cQ2 • (ρ.Θy1 * ρ.Θdps) := by sorry
