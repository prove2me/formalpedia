-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_theta_eq_conjugate
-- name    : DyckAlgebra.DyckRepU.theta_eq_conjugate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:07:46.544933+00:00
-- url     : https://prove2.me/theorems/e5c2bf8c-c7d9-4ff6-ab70-3ef015b87bd7
-- title:
--   Dyck Rep U: theta eq conjugate
-- statement:
--   The abstract conjugation argument used in
--   `Θ(L) = Θ(u) L Θ(u)⁻¹`.  No left-inverse hypothesis is needed.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L247-L253
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean#L247-L253

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.theta_eq_conjugate {L thetaL U Uinv : ρ.carrier}
    (hintertwine : U * L = thetaL * U) (hright : U * Uinv = 1) :
    thetaL = U * L * Uinv := by sorry
