-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_theta_comm_dp_dm
-- name    : DyckAlgebra.DyckRepU.theta_comm_dp_dm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:05:35.695319+00:00
-- url     : https://prove2.me/theorems/b389094c-46d0-4706-98b6-c7693a9db00c
-- title:
--   Dyck Rep U: theta comm dp dm
-- statement:
--   Replacing `d₊` by `Θ(d₊)=(1-s)d₊` left-multiplies its commutator
--   with `d₋` by `1-s`.  This is the basic reason that the derived `y₁` formula
--   transforms without adding `y₁` as independent data.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L272-L279
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Theta.lean#L272-L279

import Definitions.Def_RequestProject_Aqt_Rep
import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
open DyckAlgebra
open scoped BigOperators
universe v
attribute [instance] ThetaData.ring ThetaData.algebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.theta_comm_dp_dm :
    ρ.Θdp * ρ.dm - ρ.dm * ρ.Θdp =
      (1 - ρ.sElt) * (ρ.dp * ρ.dm - ρ.dm * ρ.dp) := by sorry
