-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_intertwine_dGammaTail
-- name    : DyckAlgebra.DyckRepU.intertwine_dGammaTail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:07:36.846794+00:00
-- url     : https://prove2.me/theorems/87ee6fa1-dac9-496c-880e-7cc2c85aed5a
-- title:
--   Dyck Rep U: intertwine d Gamma Tail
-- statement:
--   Intertwining for the repeated tail of a `D_γ` word.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L168-L201
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L168-L201

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.intertwine_dGammaTail (U : ρ.carrier)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U) :
    ∀ gs : List ℕ, U * ρ.dGammaTail gs = ρ.thetaDGammaTail gs * U := by sorry
