-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_intertwine_dGamma
-- name    : DyckAlgebra.DyckRepU.intertwine_dGamma
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:07:42.826205+00:00
-- url     : https://prove2.me/theorems/438c4c6e-fed9-40de-9a84-2fd5421a2a83
-- title:
--   Dyck Rep U: intertwine d Gamma
-- statement:
--   **Commutation of `Θ` with `D_γ`.**  An operator which intertwines each
--   constituent generator with its `Θ`-image intertwines the complete `D_γ` word.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L234-L243
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L234-L243

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.intertwine_dGamma (U : ρ.carrier)
    (hm : U * ρ.dm = ρ.dm * U)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U) :
    ∀ γ : List ℕ, U * ρ.dGamma γ = ρ.thetaDGamma γ * U := by sorry
