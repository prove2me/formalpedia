-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_theta_comm_dps_dm
-- name    : DyckAlgebra.DyckRepU.theta_comm_dps_dm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:06:00.67806+00:00
-- url     : https://prove2.me/theorems/d28ac1f3-dcd6-4258-9201-20686689354e
-- title:
--   Dyck Rep U: theta comm dps dm
-- statement:
--   Replacing `d₊*` by `Θ(d₊*)=minv d₊*` left-multiplies its commutator
--   with `d₋` by `minv`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L346-L351
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L346-L351

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.theta_comm_dps_dm :
    ρ.Θdps * ρ.dm - ρ.dm * ρ.Θdps =
      ρ.minv * (ρ.dps * ρ.dm - ρ.dm * ρ.dps) := by sorry
