-- Prove2me | Theorems.Thm_DyckAlgebra_DyckRepU_theta_preserve_I2_scalar_via_sStar
-- name    : DyckAlgebra.DyckRepU.theta_preserve_I2_scalar_via_sStar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T23:07:20.65281+00:00
-- url     : https://prove2.me/theorems/ff5e1347-43b2-4b40-978b-d7274e0206ac
-- title:
--   Dyck Rep U: theta preserve I2 scalar via s Star
-- statement:
--   **Scalar form of general-level `(I2)` preservation.**
--
--   This is the form needed by the source, whose level-`k` annihilator
--   relation is `(d_+ + q^k y_1 d_+^*) (d_+^*)^k ε₀ = 0`.  The scalar `a` is kept
--   general here; the corresponding level value of `(Q2)` is
--   `cQ2 = -a`.
--
--   Source: https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean#L152-L162
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean#L152-L162

import Definitions.Def_RequestProject_Aqt_Theta
import Definitions.Def_RequestProject_Aqt_PreserveKernel
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)

theorem DyckAlgebra.DyckRepU.theta_preserve_I2_scalar_via_sStar (a : 𝕜) (k : ℕ) (e0 : ρ.carrier)
    (hcQ2 : cQ2 = -a)
    (hsStar : ∀ j, 1 ≤ j → ρ.sStarElt * ρ.dps ^ j * e0 = 0)
    (hI2 : (ρ.dp + a • (ρ.yy 1 * ρ.dps)) * ρ.dps ^ k * e0 = 0) :
    (ρ.Θdp + a • (ρ.Θy1 * ρ.Θdps)) * ρ.Θdps ^ k * e0 = 0 := by sorry
