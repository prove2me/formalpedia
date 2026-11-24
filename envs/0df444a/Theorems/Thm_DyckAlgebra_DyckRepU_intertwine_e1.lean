-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_intertwine_e1
-- name    : DyckAlgebra.DyckRepU.intertwine_e1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:23:23.256653+00:00
-- url     : https://prove2.me/theorems/02e13232-5d1b-43ca-8e1a-d2dd591602c7
-- title:
--   Dyck Rep U: intertwine e1
-- statement:
--   Operator-form `Θ`--`e₁` commutation at level zero:
--   `U e₁ = (e₁ + positive-series - D₁) U`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L143-L156
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L143-L156

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.intertwine_e1 (U : ρ.carrier) (hlevel : ρ.level = 0)
    (hm : U * ρ.dm = ρ.dm * U)
    (hp : U * ρ.dp = ρ.Θdp * U) :
    U * ρ.e1Word =
      (ρ.e1Word + (ρ.dPositiveSeries - ρ.dOneWord)) * U := by sorry
