-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_thetaDGamma_eq_conjugate
-- name    : DyckAlgebra.DyckRepU.thetaDGamma_eq_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:24:12.879611+00:00
-- url     : https://prove2.me/theorems/68c328ef-1682-4c72-8d2d-7aca3451e833
-- title:
--   Dyck Rep U: theta DGamma eq conjugate
-- statement:
--   The transformed `D_γ` word is conjugate to `D_γ` by any invertible operator
--   implementing `Θ` on its generators.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L257-L266
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L257-L266

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.thetaDGamma_eq_conjugate (γ : List ℕ) (U Uinv : ρ.carrier)
    (hm : U * ρ.dm = ρ.dm * U)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U)
    (hright : U * Uinv = 1) :
    ρ.thetaDGamma γ = U * ρ.dGamma γ * Uinv := by sorry
