-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_theta_preserve_I2_qpow_via_sStar
-- name    : DyckAlgebra.DyckRepU.theta_preserve_I2_qpow_via_sStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:07:31.541842+00:00
-- url     : https://prove2.me/theorems/aca55864-878b-40cb-9c07-3f27fc49b232
-- title:
--   Dyck Rep U: theta preserve I2 qpow via s Star
-- statement:
--   **The source's level-`k` `(I2)` relation is preserved by `Θ`.**
--
--   Here the coefficient is exactly `q^k`, and `(Q2)` consequently has coefficient
--   `-q^k`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean#L170-L175
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean#L170-L175

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_PreserveKernel
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.theta_preserve_I2_qpow_via_sStar (k : ℕ) (e0 : ρ.carrier)
    (hcQ2 : cQ2 = -(q ^ k))
    (hsStar : ∀ j, 1 ≤ j → ρ.sStarElt * ρ.dps ^ j * e0 = 0)
    (hI2 : (ρ.dp + (q ^ k) • (ρ.yy 1 * ρ.dps)) * ρ.dps ^ k * e0 = 0) :
    (ρ.Θdp + (q ^ k) • (ρ.Θy1 * ρ.Θdps)) * ρ.Θdps ^ k * e0 = 0 := by sorry
