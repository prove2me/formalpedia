-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_intertwine_dGamma_cons
-- name    : DyckAlgebra.DyckRepU.intertwine_dGamma_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:08:01.183423+00:00
-- url     : https://prove2.me/theorems/296ab8d1-eed1-4653-b56b-6bea2cedb2c4
-- title:
--   Dyck Rep U: intertwine d Gamma cons
-- statement:
--   The one-block assembly step for intertwining a `D_γ` word.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L204-L230
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L204-L230

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.intertwine_dGamma_cons (U : ρ.carrier) (g : ℕ) (gs : List ℕ)
    (hm : U * ρ.dm = ρ.dm * U)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U) :
    U * ρ.dGamma (g :: gs) = ρ.thetaDGamma (g :: gs) * U := by sorry
